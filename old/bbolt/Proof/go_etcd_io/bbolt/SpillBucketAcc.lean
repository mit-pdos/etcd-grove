/-
`Bucket.spill`'s access to the transaction during the spill (`spillR`): one bucket's objects
and capacities out of it (`spillR_at`), and back changed.
-/
module

public import Proof.go_etcd_io.bbolt.SpillState

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section own
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- The capacities of a bucket's nodes outside `K`. -/
def capsB (B : BRec) (K : Loc → Bool) : IProp GF :=
  [∗map] l ↦ r ∈ B.ns, if K l then iprop(emp) else capOwn r

/-- The transaction's page buffers. -/
def bufsOwn (T : WTx) : IProp GF :=
  [∗map] id ↦ p ∈ T.pm, iprop(∃ bs, ⌜T.bufs !! id = some bs⌝ ∗ bytesPointsto p (DFrac.own 1) bs)

/-- The ghost map's authority, its domain the pages of the view and the dirty ones. -/
def ghostOK (γ : GName) (W : WView) (T : WTx) : IProp GF :=
  iprop(∃ M : GMap Nat Unit, ghostMapAuth γ 1 M ∗
    ⌜∀ id, (M !! id).isSome ↔ (spillPages W T !! id).isSome⌝)

/-- The buckets but `bl`, with their capacities. -/
def othersOwn (W : WView) (bs : GMap Loc BRec) (bl : Loc) (K : Loc → Bool) : IProp GF :=
  [∗map] b ↦ C ∈ Std.delete bs bl, iprop(bktOwnX W b C ∗ capsB C K)

theorem spillR_at (I : FLImpl (GF := GF)) (γd : DBNames) (γ : GName) (W : WView) (txl : Loc)
    (txid : w64) (T : WTx) (ρ : DBState) (F : GMap Nat (List w8)) (K : Loc → Bool) (bl : Loc)
    (B : BRec) (hB : T.bs !! bl = some B) :
    spillR I γd γ W txl txid T ρ F K ⊣⊢
      dbWR I γd W txl txid ρ ∗ wView W ∗ TxW_rest_root txl (DFrac.own 1) T.t ∗
      T.t.meta' ↦ T.mv ∗ T.t.pages' ↦$ T.pm ∗ bufsOwn T ∗ bktOwnX W bl B ∗ capsB B K ∗
      othersOwn W T.bs bl K ∗ ghostOK γ W T ∗ pgToks γ F := by
  unfold spillR ownWriteTxGX capsOwn othersOwn bufsOwn ghostOK capsB
  have hB' : Std.get? T.bs bl = some B := hB
  have e1 := BigSepM.bigSepM_delete (M := GMap Loc) (Φ := fun b C => bktOwnX (GF := GF) W b C) hB'
  have e2 := BigSepM.bigSepM_delete (M := GMap Loc)
    (Φ := fun (_ : Loc) (C : BRec) => iprop([∗map] l ↦ r ∈ C.ns,
      if K l then iprop(emp) else capOwn (GF := GF) r)) hB'
  have e3 : ([∗map] b ↦ C ∈ Std.delete T.bs bl, iprop(bktOwnX (GF := GF) W b C ∗
      [∗map] l ↦ r ∈ C.ns, if K l then iprop(emp) else capOwn (GF := GF) r)) ⊣⊢
      ([∗map] b ↦ C ∈ Std.delete T.bs bl, bktOwnX (GF := GF) W b C) ∗
      [∗map] _b ↦ C ∈ Std.delete T.bs bl, [∗map] l ↦ r ∈ C.ns,
        if K l then iprop(emp) else capOwn (GF := GF) r :=
    BiEntails.of_eq BigSepM.bigSepM_sep_eq
  constructor
  · iintro ⟨Hdb, ⟨Ht, Hm, Hpm, Hbufs, Hbs⟩, Hv, Hcaps, Hg, HF⟩
    icases e1.1 $$ Hbs with ⟨Hb, Hbs⟩
    icases e2.1 $$ Hcaps with ⟨Hc, Hcaps⟩
    ihave Ho := e3.2 $$ [Hbs Hcaps]
    · iframe
    iframe
  · iintro ⟨Hdb, Hv, Ht, Hm, Hpm, Hbufs, Hb, Hc, Ho, Hg, HF⟩
    icases e3.1 $$ Ho with ⟨Hbs, Hcaps⟩
    ihave Hbs := e1.2 $$ [Hb Hbs]
    · iframe
    ihave Hcaps := e2.2 $$ [Hc Hcaps]
    · iframe
    iframe

/-- The bucket `bl` changed: `othersOwn` of the transaction with it changed is the same. -/
theorem othersOwn_insert (W : WView) (bs : GMap Loc BRec) (bl : Loc) (B' : BRec)
    (K : Loc → Bool) :
    othersOwn (GF := GF) W (<[bl := B']> bs) bl K = othersOwn W bs bl K := by
  unfold othersOwn
  congr 1
  show GMap.delete bl (<[bl := B']> bs) = GMap.delete bl bs
  apply GMap.ext; intro k
  by_cases e : bl = k
  · subst e; rw [GMap.lookup_delete, GMap.lookup_delete]
  · rw [GMap.lookup_delete_ne _ e, GMap.lookup_delete_ne _ e, GMap.lookup_insert_ne _ _ e]

/-- A bucket whose nodes all have their capacities: `bktOwn`. -/
theorem bktOwn_of_X (W : WView) (bl : Loc) (B : BRec) (K : Loc → Bool)
    (hK : ∀ l r, B.ns !! l = some r → K l = false) :
    bktOwnX (GF := GF) W bl B ∗ capsB B K ⊢ bktOwn W bl B := by
  iintro ⟨Hb, Hc⟩
  iapply (bktOwn_X W bl B).2
  iframe Hb
  unfold capsB
  iapply (BigSepM.bigSepM_mono (M := GMap Loc) ?_) $$ Hc
  intro l r hr
  rw [hK l r hr]
  exact .rfl

theorem bktOwn_to_X (W : WView) (bl : Loc) (B : BRec) (K : Loc → Bool) :
    bktOwn (GF := GF) W bl B ⊢ bktOwnX W bl B ∗ capsB B K := by
  iintro Hb
  icases (bktOwn_X W bl B).1 $$ Hb with ⟨Hb, Hc⟩
  iframe Hb
  unfold capsB
  iapply (BigSepM.bigSepM_mono (M := GMap Loc) ?_) $$ Hc
  intro l r _
  cases K l
  · exact .rfl
  · exact Affine.affine

theorem capsB_ns (B B' : BRec) (K : Loc → Bool) (h : B'.ns = B.ns) :
    capsB (GF := GF) B' K = capsB B K := by unfold capsB; rw [h]

theorem bufsOwn_eq (T T' : WTx) (hpm : T'.pm = T.pm) (hb : T'.bufs = T.bufs) :
    bufsOwn (GF := GF) T' = bufsOwn T := by unfold bufsOwn; rw [hpm, hb]

theorem ghostOK_eq (γ : GName) (W : WView) (T T' : WTx) (hb : T'.bufs = T.bufs) :
    ghostOK (GF := GF) γ W T' = ghostOK γ W T := by unfold ghostOK spillPages; rw [hb]

theorem pageOwn_eq (W : WView) (B B' : BRec) (hp : B'.bv.page' = B.bv.page') (hi : B'.isrc = B.isrc)
    (hg : B'.ipg = B.ipg) : pageOwn (GF := GF) W B' = pageOwn W B := by
  unfold pageOwn; rw [hp, hi, hg]

/-- A big separating conjunction over a map's keys, listed. -/
theorem keys_bigSepM {V : Type} (Φ : GoString → IProp GF) (m : GMap GoString V)
    (keys : List GoString) (hk : ∀ k, k ∈ keys ↔ (m !! k).isSome) (hn : keys.Nodup) :
    ([∗list] k ∈ keys, Φ k) ⊣⊢ [∗map] k ↦ _x ∈ m, Φ k := by
  have hp : keys.Perm (m.toList.map Prod.fst) := by
    rw [List.perm_ext_iff_of_nodup hn (GMap.toList_keys_nodup m)]
    intro k
    rw [hk k, List.mem_map]
    constructor
    · intro h
      obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 h
      exact ⟨(k, v), (GMap.mem_toList m k v).2 hv, rfl⟩
    · rintro ⟨⟨k', v⟩, hm, rfl⟩
      rw [(GMap.mem_toList m k' v).1 hm]; rfl
  refine (BigSepL.bigSepL_perm (Φ := Φ) hp).trans ?_
  refine (BiEntails.of_eq (BigSepL.bigSepL_map (Φ := fun _ k => Φ k) Prod.fst)).trans ?_
  exact (BigSepM.bigSepM_toList (Φ := fun k (_ : V) => Φ k) (m := m)).symm

end own

end bbolt
end EtcdGrove
end Perennial
