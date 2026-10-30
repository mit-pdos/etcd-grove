/-
`sort.Sort(n.children)` in `node.spill`: the children's structs, inodes and first keys lent out
of the spill state (the view's keys at fractions of it, `pv_list`, `srcBorrowD`), and back with
`n.children` permuted.
-/
module

public import Proof.go_etcd_io.bbolt.SpillNodeAcc
public import Proof.go_etcd_io.bbolt.WriteDeref
public import Proof.go_etcd_io.bbolt.SpillDeref
public import Proof.go_etcd_io.bbolt.SpillBucketAcc

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

/-- The first entry of a list of entries (a default for none). -/
def wHead (ws : List WEntry) : WEntry := ws.headD ⟨W32 0, W64 0, [], [], Src.stale, Src.stale⟩

/-- What `sort.Sort` reads of the children: their structs, inodes, first keys at fractions. -/
def sortF (ns : GMap Loc NRec) (c : Loc) : node := ((ns !! c).map NRec.nv).getD (zero_val node)
def sortG (ns : GMap Loc NRec) (c : Loc) : List Inode := ((ns !! c).map NRec.ins).getD []
def sortK (ns : GMap Loc NRec) (c : Loc) : List w8 := ((ns !! c).map (fun rc => (wHead rc.ws).key)).getD []
def sortQ (ns : GMap Loc NRec) (q : Loc → Qp) (c : Loc) : DFrac :=
  ((ns !! c).map (fun rc => srcFrac (wHead rc.ws).ks (q c))).getD (DFrac.own 1)

/-- What `sort.Sort` reads, as its spec takes it. -/
def sortRes (ns : GMap Loc NRec) (q : Loc → Qp) (cs : List Loc) : IProp GF :=
  [∗list] c ∈ cs, iprop(c ↦ sortF ns c ∗ (sortF ns c).inodes' ↦* sortG ns c ∗
    ((sortG ns c).headD (zero_val Inode)).key' ↦*{sortQ ns q c} sortK ns c)

/-- What `sort.Sort` reads of one child, out of its node and a fraction of the view. -/
theorem child_sort (W : WView) (hc : W.data.locCar ≠ 0) (ns : GMap Loc NRec) (qf : Loc → Qp)
    (c : Loc) (rc : NRec) (hrc : ns !! c = some rc) (h0 : 0 < rc.ws.length)
    (hl : rc.ins.length = rc.ws.length) (hlive : wsLive rc.ws) :
    nodeOwnX (GF := GF) W c rc ∗ pagesView W.data W.ps (qf c) W.pages ⊢
      iprop(c ↦ sortF ns c ∗ (sortF ns c).inodes' ↦* sortG ns c ∗
        ((sortG ns c).headD (zero_val Inode)).key' ↦*{sortQ ns qf c} sortK ns c) ∗
      (iprop(c ↦ sortF ns c ∗ (sortF ns c).inodes' ↦* sortG ns c ∗
        ((sortG ns c).headD (zero_val Inode)).key' ↦*{sortQ ns qf c} sortK ns c) -∗
        nodeOwnX W c rc ∗ pagesView W.data W.ps (qf c) W.pages) := by
  obtain ⟨w, ws', hws⟩ : ∃ w ws', rc.ws = w :: ws' := by
    cases h : rc.ws with
    | nil => rw [h] at h0; simp at h0
    | cons w ws' => exact ⟨w, ws', rfl⟩
  obtain ⟨it, ins', hins⟩ : ∃ it ins', rc.ins = it :: ins' := by
    cases h : rc.ins with
    | nil => rw [h, hws] at hl; simp at hl
    | cons it ins' => exact ⟨it, ins', rfl⟩
  have eF : sortF ns c = rc.nv := by unfold sortF; rw [hrc]; rfl
  have eG : sortG ns c = rc.ins := by unfold sortG; rw [hrc]; rfl
  have eK : sortK ns c = w.key := by unfold sortK wHead; rw [hrc]; simp [hws]
  have eQ : sortQ ns qf c = srcFrac w.ks (qf c) := by unfold sortQ wHead; rw [hrc]; simp [hws]
  have hns : w.ks ≠ Src.stale := (hlive w (by rw [hws]; exact List.mem_cons_self)).1
  rw [eF, eG, eK, eQ, hins]
  simp only [List.headD_cons]
  unfold nodeOwnX
  rw [hins, hws]
  iintro ⟨⟨Hn, Hi, Hents, Hch, Hcap, Hkey⟩, Hpv⟩
  icases BigSepL2.bigSepL2_cons.1 $$ Hents with ⟨Hw, Hents⟩
  unfold wOwn
  icases Hw with ⟨%hfp, Hk, Hv⟩
  icases srcBorrowD W hc (qf c) it.key' w.ks w.key hns $$ [Hpv Hk] with ⟨Hkb, Hkback⟩
  · iframe
  iframe Hn Hi Hkb
  iintro ⟨Hn, Hi, Hkb⟩
  icases Hkback $$ Hkb with ⟨Hpv, Hk⟩
  iframe Hpv Hn Hi Hch Hcap Hkey
  iapply BigSepL2.bigSepL2_cons.2
  iframe Hents
  iframe
  ipureintro; exact hfp

/-- The node `n`'s children `r.cs` lent to `sort.Sort`, and back with `n.children` permuted. -/
theorem spillR_sort (I : FLImpl (GF := GF)) (γd : DBNames) (γ : GName) (W : WView) (txl : Loc)
    (txid : w64) (T : WTx) (ρ : DBState) (F : GMap Nat (List w8)) (K : Loc → Bool) (bl : Loc)
    (B : BRec) (n : Loc) (r : NRec) (hB : T.bs !! bl = some B) (hn : B.ns !! n = some r)
    (hnd : r.cs.Nodup) (hnc : n ∉ r.cs) (hcar : W.data.locCar ≠ 0)
    (hc : ∀ c ∈ r.cs, ∃ rc, B.ns !! c = some rc ∧ 0 < rc.ws.length ∧
      rc.ins.length = rc.ws.length ∧ wsLive rc.ws) :
    spillR I γd γ W txl txid T ρ F K ⊢ ∃ q : Loc → Qp,
      r.nv.children' ↦* r.cs ∗ sortRes B.ns q r.cs ∗
      (∀ ys, ⌜ys.Perm r.cs⌝ -∗ r.nv.children' ↦* ys -∗ sortRes B.ns q r.cs -∗
        spillR I γd γ W txl txid (setB T bl (setN B n { r with cs := ys })) ρ F K) := by
  have hdel : ∀ c, c ≠ n → (Std.delete B.ns n : GMap Loc NRec) !! c = B.ns !! c := by
    intro c hne; show (GMap.delete n B.ns) !! c = B.ns !! c
    exact GMap.lookup_delete_ne _ (Ne.symm hne)
  have hdom : ∀ c ∈ r.cs, ((Std.delete B.ns n : GMap Loc NRec) !! c).isSome := by
    intro c hc'
    obtain ⟨rc, hrc, -⟩ := hc c hc'
    rw [hdel c (fun e => hnc (e ▸ hc')), hrc]; rfl
  iintro HR
  icases (spillR_at I γd γ W txl txid T ρ F K bl B hB).1 $$ HR
    with ⟨Hdb, Hv, Ht, Hm, Hpm, Hbufs, Hb, Hc, Ho, Hg, HF⟩
  isimp only [bktOwnX] at Hb
  icases Hb with ⟨Hbv, Hib, Hnm, Hbm, Hpo, Hns⟩
  icases (BigSepM.bigSepM_delete (M := GMap Loc) (Φ := fun l r => nodeOwnX (GF := GF) W l r)
    (show Std.get? B.ns n = some r from hn)).1 $$ Hns with ⟨Hn, Hns⟩
  icases map_split (fun l r => nodeOwnX (GF := GF) W l r) r.cs (Std.delete B.ns n) hnd hdom $$ Hns
    with ⟨Hks, %m', %hm', Hm'⟩
  isimp only [wView] at Hv
  icases Hv with ⟨Hd, #Hps, #Hlg, Hfl, #Hdl, %Hlgv, Hpv⟩
  icases pv_list W r.cs W.q hnd $$ Hpv with ⟨Hpvs, Hpvback⟩
  ihave Hzip := BigSepL.bigSepL_sep_eqv_symm.1 $$ [Hks Hpvs]
  · iframe
  ihave Hzip2 := (BigSepL.bigSepL_mono (Ψ := fun _ c =>
      iprop(iprop(c ↦ sortF B.ns c ∗ (sortF B.ns c).inodes' ↦* sortG B.ns c ∗
        ((sortG B.ns c).headD (zero_val Inode)).key' ↦*{sortQ B.ns (fracOf r.cs W.q) c} sortK B.ns c) ∗
      (iprop(c ↦ sortF B.ns c ∗ (sortF B.ns c).inodes' ↦* sortG B.ns c ∗
        ((sortG B.ns c).headD (zero_val Inode)).key' ↦*{sortQ B.ns (fracOf r.cs W.q) c} sortK B.ns c) -∗
        (∃ v, ⌜(Std.delete B.ns n : GMap Loc NRec) !! c = some v⌝ ∗ nodeOwnX W c v) ∗
          pagesView W.data W.ps (fracOf r.cs W.q c) W.pages))) ?_) $$ Hzip
  · intro k c hk
    have hcm : c ∈ r.cs := List.mem_of_getElem? hk
    obtain ⟨rc, hrc, h0, hl, hlive⟩ := hc c hcm
    iintro ⟨Hp, ⟨%v, %hv, Hnv⟩⟩
    rw [hdel c (fun e => hnc (e ▸ hcm)), hrc] at hv
    cases hv
    icases child_sort W hcar B.ns (fracOf r.cs W.q) c rc hrc h0 hl hlive $$ [Hnv Hp] with ⟨Hit, Hw⟩
    · iframe
    iframe Hit
    iintro Hit
    icases Hw $$ Hit with ⟨Hnv, Hp⟩
    iframe Hp
    iexists rc
    iframe Hnv
    ipureintro
    rw [hdel c (fun e => hnc (e ▸ hcm)), hrc]
  icases BigSepL.bigSepL_sep_eqv.1 $$ Hzip2 with ⟨Hits, Hws⟩
  isimp only [nodeOwnX] at Hn
  icases Hn with ⟨Hnn, Hins, Hents, Hch, Hchcap, Hkey⟩
  iexists (fracOf r.cs W.q)
  iframe Hch
  isplitl [Hits]
  · unfold sortRes; iexact Hits
  iintro %ys %hperm Hch Hits
  unfold sortRes
  ihave Hzip3 := BigSepL.bigSepL_wand $$ Hits Hws
  icases BigSepL.bigSepL_sep_eqv.1 $$ Hzip3 with ⟨Hks, Hpvs⟩
  ihave Hpv := Hpvback $$ Hpvs
  have hnone : ∀ l ∈ r.cs, m' !! l = none := by
    intro l hl; rw [hm' l, if_pos hl]
  icases list_into_map (fun l r => nodeOwnX (GF := GF) W l r)
    (fun l v => (Std.delete B.ns n : GMap Loc NRec) !! l = some v) r.cs m' hnd hnone $$ [Hm' Hks]
    with ⟨%M', %hM', HM'⟩
  · iframe
  have hMe : M' = Std.delete B.ns n := by
    apply GMap.ext; intro l
    obtain ⟨hd1, hd2⟩ := hM'
    by_cases hl : l ∈ r.cs
    · cases hx : M' !! l with
      | none =>
        have := (hd1 l).2 (Or.inr hl); rw [hx] at this; cases this
      | some v =>
        rcases hd2 l v hx with h | h
        · rw [hm' l, if_pos hl] at h; cases h
        · exact h.symm
    · have e := hm' l; rw [if_neg hl] at e
      cases hx : M' !! l with
      | none =>
        cases hy : (Std.delete B.ns n : GMap Loc NRec) !! l with
        | none => rfl
        | some y =>
          have : (M' !! l).isSome := (hd1 l).2 (Or.inl (by rw [e, hy]; rfl))
          rw [hx] at this; cases this
      | some v =>
        rcases hd2 l v hx with h | h
        · rw [e] at h; exact h.symm
        · exact h.symm
  subst hMe
  have hB' : (setB T bl (setN B n { r with cs := ys })).bs !! bl = some (setN B n { r with cs := ys }) :=
    GMap.lookup_insert _ _ _
  iapply (spillR_at I γd γ W txl txid _ ρ F K bl _ hB').2
  have e1 : bufsOwn (GF := GF) (setB T bl (setN B n { r with cs := ys })) = bufsOwn T := rfl
  have e2 : ghostOK (GF := GF) γ W (setB T bl (setN B n { r with cs := ys })) = ghostOK γ W T := rfl
  have e3 : othersOwn (GF := GF) W (setB T bl (setN B n { r with cs := ys })).bs bl K =
      othersOwn W T.bs bl K := othersOwn_insert W T.bs bl _ K
  rw [e1, e2, e3]
  dsimp only [setB]
  iframe Hdb Ht Hm Hpm Hbufs Ho Hg HF
  isplitl [Hd Hfl Hpv]
  · unfold wView; iframe; iframe #; ipureintro; exact Hlgv
  isplitl [Hbv Hib Hnm Hbm Hpo HM' Hnn Hins Hents Hch Hchcap Hkey]
  · unfold bktOwnX setN
    rw [show pageOwn W { B with ns := <[n := { r with cs := ys }]> B.ns } = pageOwn W B from rfl]
    iframe Hbv Hib Hnm Hbm Hpo
    iapply (BigSepM.bigSepM_insert_delete (M := GMap Loc) (m := B.ns) (i := n)
      (x := { r with cs := ys }) (Φ := fun l r => nodeOwnX (GF := GF) W l r)).2
    iframe HM'
    unfold nodeOwnX
    iframe
  · unfold capsB setN
    icases (BigSepM.bigSepM_delete (M := GMap Loc)
      (Φ := fun l r => if K l then iprop(emp) else capOwn (GF := GF) r)
      (show Std.get? B.ns n = some r from hn)).1 $$ Hc with ⟨Hcn, Hc⟩
    iapply (BigSepM.bigSepM_insert_delete (M := GMap Loc) (m := B.ns) (i := n)
      (x := { r with cs := ys })
      (Φ := fun l r => if K l then iprop(emp) else capOwn (GF := GF) r)).2
    iframe

theorem sortG_ne (ns : GMap Loc NRec) (cs : List Loc)
    (hc : ∀ c ∈ cs, ∃ rc, ns !! c = some rc ∧ 0 < rc.ws.length ∧
      rc.ins.length = rc.ws.length ∧ wsLive rc.ws) : ∀ c ∈ cs, sortG ns c ≠ [] := by
  intro c hc'
  obtain ⟨rc, hrc, h1, h2, -⟩ := hc c hc'
  unfold sortG; rw [hrc]; simp only [Option.map_some, Option.getD_some]
  intro h; rw [h] at h2; simp at h2; omega

end own

end bbolt
end EtcdGrove
end Perennial
