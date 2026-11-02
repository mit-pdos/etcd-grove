/-
Access to a node of the spill state (`spillR`): its struct and its bucket's, and back changed.
-/
module

public import Proof.go_etcd_io.bbolt.SpillNodeRec
public import Proof.go_etcd_io.bbolt.SpillNodeForest

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section pure
variable [ext : FfiSyntax]

/-- `T` with the bucket `bl`'s record `B'`. -/
def setB (T : WTx) (bl : Loc) (B' : BRec) : WTx := { T with bs := <[bl := B']> T.bs }

/-- The bucket `B` with the node `l`'s record `r`. -/
def setN (B : BRec) (l : Loc) (r : NRec) : BRec := { B with ns := <[l := r]> B.ns }

theorem spillFrame_transN (T1 T2 T3 : WTx) (X Y : Loc → Prop) (h1 : spillFrame T1 T2 X)
    (h2 : spillFrame T2 T3 Y) (hY : ∀ c, Y c → X c) : spillFrame T1 T3 X := by
  obtain ⟨a1, b1, c1, d1, e1, f1⟩ := h1
  obtain ⟨a2, b2, c2, d2, e2, f2⟩ := h2
  refine ⟨fun c => (a1 c).trans (a2 c), b2.trans b1, Nat.le_trans c1 c2,
    GMap.map_subseteq_trans d1 d2, ?_, ?_⟩
  · rw [e2, e1]
  · intro c C C' hX hC hC'
    obtain ⟨C2, hC2⟩ := Option.isSome_iff_exists.1 ((a1 c).1 (by rw [hC]; rfl))
    have hY' : ¬ Y c := fun h => hX (hY c h)
    obtain ⟨s1, k1⟩ := f1 c C C2 hX hC hC2
    obtain ⟨s2, k2⟩ := f2 c C2 C' hY' hC2 hC'
    refine ⟨derefStarX_trans _ _ _ s1 s2, fun l r r' hr hr' => ?_⟩
    obtain ⟨r2, hr2⟩ := derefStarX_ns C2 C' s2 l r' hr'
    rw [k2 l r2 r' hr2 hr', k1 l r r2 hr hr2]

theorem spillFrame_reflN (T : WTx) (X : Loc → Prop) : spillFrame T T X := by
  refine ⟨fun _ => Iff.rfl, rfl, Nat.le_refl _, GMap.map_subseteq_refl _, rfl, ?_⟩
  intro c C C' _ hC hC'
  rw [hC] at hC'; cases hC'
  refine ⟨Or.inl rfl, fun l r r' hr hr' => ?_⟩
  rw [hr] at hr'; cases hr'; rfl

/-- Only the bucket `bl` changed. -/
theorem spillFrame_setB (T : WTx) (bl : Loc) (B' : BRec) (hbl : (T.bs !! bl).isSome) :
    spillFrame T (setB T bl B') (· = bl) := by
  refine ⟨fun c => ?_, rfl, Nat.le_refl _, GMap.map_subseteq_refl _, rfl, ?_⟩
  · by_cases e : bl = c
    · subst e; show _ ↔ ((<[bl := B']> T.bs) !! bl).isSome
      rw [GMap.lookup_insert]; simp [hbl]
    · show _ ↔ ((<[bl := B']> T.bs) !! c).isSome
      rw [GMap.lookup_insert_ne _ _ e]
  · intro c C C' hc hC hC'
    have e : bl ≠ c := fun h => hc h.symm
    change (<[bl := B']> T.bs) !! c = some C' at hC'
    rw [GMap.lookup_insert_ne _ _ e, hC] at hC'
    cases hC'
    refine ⟨Or.inl rfl, fun l r r' hr hr' => ?_⟩
    rw [hr] at hr'; cases hr'; rfl

end pure

section own
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- A node's struct and its children, out of the spill state, and back unchanged. -/
theorem spillR_kids (I : FLImpl (GF := GF)) (γd : DBNames) (γ : GName) (W : WView) (txl : Loc)
    (txid : w64) (T : WTx) (ρ : DBState) (F : GMap Nat (List w8)) (K : Loc → Bool) (bl : Loc)
    (B : BRec) (n : Loc) (r : NRec) (hB : T.bs !! bl = some B) (hn : B.ns !! n = some r) :
    spillR I γd γ W txl txid T ρ F K ⊢
      n ↦ r.nv ∗ r.nv.children' ↦* r.cs ∗
      (n ↦ r.nv -∗ r.nv.children' ↦* r.cs -∗ spillR I γd γ W txl txid T ρ F K) := by
  unfold spillR ownWriteTxGX
  iintro ⟨Hdb, ⟨Hrest, Hm, Hpm, Hbufs, Hbs⟩, Hv, Hcaps, Hgh, HF⟩
  icases (BigSepM.bigSepM_lookup_acc (M := GMap Loc) (Φ := fun bl B => bktOwnX (GF := GF) W bl B)
    (show Std.get? T.bs bl = some B from hB)).1 $$ Hbs with ⟨Hb, Hbback⟩
  unfold bktOwnX
  icases Hb with ⟨Hbv, Hib, Hnm, Hbm, Hpo, Hns⟩
  icases (BigSepM.bigSepM_lookup_acc (M := GMap Loc) (Φ := fun l r => nodeOwnX (GF := GF) W l r)
    (show Std.get? B.ns n = some r from hn)).1 $$ Hns with ⟨Hnd, Hnsback⟩
  unfold nodeOwnX
  icases Hnd with ⟨Hn, Hins, Hents, Hch, Hrest2⟩
  iframe Hn Hch
  iintro Hn Hch
  iframe
  iapply Hbback
  iframe
  iapply Hnsback
  iframe

/-- A node's struct and its bucket's, out of the spill state, and back unchanged. -/
theorem spillR_node (I : FLImpl (GF := GF)) (γd : DBNames) (γ : GName) (W : WView) (txl : Loc)
    (txid : w64) (T : WTx) (ρ : DBState) (F : GMap Nat (List w8)) (K : Loc → Bool) (bl : Loc)
    (B : BRec) (n : Loc) (r : NRec) (hB : T.bs !! bl = some B) (hn : B.ns !! n = some r) :
    spillR I γd γ W txl txid T ρ F K ⊢
      n ↦ r.nv ∗ bl ↦ B.bv ∗ (n ↦ r.nv -∗ bl ↦ B.bv -∗ spillR I γd γ W txl txid T ρ F K) := by
  unfold spillR ownWriteTxGX
  iintro ⟨Hdb, ⟨Hrest, Hm, Hpm, Hbufs, Hbs⟩, Hv, Hcaps, Hgh, HF⟩
  icases (BigSepM.bigSepM_lookup_acc (M := GMap Loc) (Φ := fun bl B => bktOwnX (GF := GF) W bl B)
    (show Std.get? T.bs bl = some B from hB)).1 $$ Hbs with ⟨Hb, Hbback⟩
  unfold bktOwnX
  icases Hb with ⟨Hbv, Hib, Hnm, Hbm, Hpo, Hns⟩
  icases (BigSepM.bigSepM_lookup_acc (M := GMap Loc) (Φ := fun l r => nodeOwnX (GF := GF) W l r)
    (show Std.get? B.ns n = some r from hn)).1 $$ Hns with ⟨Hnd, Hnsback⟩
  unfold nodeOwnX
  icases Hnd with ⟨Hn, Hrest2⟩
  iframe Hn Hbv
  iintro Hn Hbv
  iframe
  iapply Hbback
  iframe
  iapply Hnsback
  iframe

/-- The capacities of a bucket's nodes outside `K`. -/
def capsKN (K : Loc → Bool) (ns : GMap Loc NRec) : IProp GF :=
  [∗map] l ↦ r ∈ ns, if K l then iprop(emp) else capOwn r

/-- A node held is no bucket's. -/
theorem bkts_excl (W : WView) (bs : GMap Loc BRec) (x : Loc) (v : node) :
    ([∗map] bl ↦ B ∈ bs, bktOwnX (GF := GF) W bl B) ∗ x ↦ v ⊢
      ⌜∀ bl B, bs !! bl = some B → B.ns !! x = none⌝ ∗
      ([∗map] bl ↦ B ∈ bs, bktOwnX W bl B) ∗ x ↦ v := by
  by_cases h : ∀ bl B, bs !! bl = some B → B.ns !! x = none
  · iintro ⟨H1, H2⟩
    iframe
    ipureintro; exact h
  · skip
    obtain ⟨bl, B, hB, r, hr⟩ : ∃ bl B, bs !! bl = some B ∧ ∃ r, B.ns !! x = some r := by
      apply Classical.byContradiction
      intro hc
      apply h
      intro bl B hB
      cases hx : B.ns !! x with
      | none => rfl
      | some r => exact absurd ⟨bl, B, hB, r, hx⟩ hc
    iintro ⟨H1, H2⟩
    icases (BigSepM.bigSepM_lookup_acc (M := GMap Loc) (Φ := fun bl B => bktOwnX (GF := GF) W bl B)
      (show Std.get? bs bl = some B from hB)).1 $$ H1 with ⟨Hb, -⟩
    unfold bktOwnX
    icases Hb with ⟨-, -, -, -, -, Hns⟩
    icases (BigSepM.bigSepM_lookup_acc (M := GMap Loc) (Φ := fun l r => nodeOwnX (GF := GF) W l r)
      (show Std.get? B.ns x = some r from hr)).1 $$ Hns with ⟨Hn, -⟩
    unfold nodeOwnX
    icases Hn with ⟨Hn, -⟩
    iexfalso
    iapply node_ptsto_excl
    iframe

/-- Nodes held are no bucket's. -/
theorem bkts_excl_ns (W : WView) (bs : GMap Loc BRec) (ns : GMap Loc NRec) :
    ([∗map] bl ↦ B ∈ bs, bktOwnX (GF := GF) W bl B) ∗ ([∗map] l ↦ r ∈ ns, nodeOwnX W l r) ⊢
      ⌜∀ bl B l, bs !! bl = some B → (ns !! l).isSome → B.ns !! l = none⌝ ∗
      ([∗map] bl ↦ B ∈ bs, bktOwnX W bl B) ∗ ([∗map] l ↦ r ∈ ns, nodeOwnX W l r) := by
  by_cases h : ∀ bl B l, bs !! bl = some B → (ns !! l).isSome → B.ns !! l = none
  · iintro ⟨H1, H2⟩
    iframe
    ipureintro; exact h
  · obtain ⟨bl, B, l, hB, hr, r, hrr⟩ : ∃ bl B l, bs !! bl = some B ∧ (ns !! l).isSome ∧
        ∃ r, B.ns !! l = some r := by
      apply Classical.byContradiction
      intro hc
      apply h
      intro bl B l hB hl
      cases hx : B.ns !! l with
      | none => rfl
      | some r => exact absurd ⟨bl, B, l, hB, hl, r, hx⟩ hc
    obtain ⟨r0, hr0⟩ := Option.isSome_iff_exists.1 hr
    iintro ⟨H1, H2⟩
    icases (BigSepM.bigSepM_lookup_acc (M := GMap Loc) (Φ := fun l r => nodeOwnX (GF := GF) W l r)
      (show Std.get? ns l = some r0 from hr0)).1 $$ H2 with ⟨Hn, -⟩
    unfold nodeOwnX
    icases Hn with ⟨Hn, -⟩
    icases bkts_excl W bs l r0.nv $$ [H1 Hn] with ⟨%hx, -, -⟩
    · iframe
    rw [hx bl B hB] at hrr; cases hrr

/-- A bucket held is disjoint from the buckets `bs` in its nodes. -/
theorem bkts_excl_b (W : WView) (bs : GMap Loc BRec) (bl : Loc) (B : BRec) :
    ([∗map] bl ↦ B ∈ bs, bktOwnX (GF := GF) W bl B) ∗ bktOwnX W bl B ⊢
      ⌜∀ b2 B2 l, bs !! b2 = some B2 → (B.ns !! l).isSome → B2.ns !! l = none⌝ ∗
      ([∗map] bl ↦ B ∈ bs, bktOwnX W bl B) ∗ bktOwnX W bl B := by
  iintro ⟨H1, H2⟩
  isimp only [bktOwnX] at H2
  icases H2 with ⟨Hbv, Hib, Hnm, Hbm, Hpo, Hns⟩
  icases bkts_excl_ns W bs B.ns $$ [H1 Hns] with ⟨%hx, H1, Hns⟩
  · iframe
  iframe H1
  isplitr
  · ipureintro; exact hx
  unfold bktOwnX
  iframe

/-- The bucket `bl` (record `B`) out of the spill state, its nodes' capacities with it; back
changed (`setB`), the capacities changed only on its nodes. -/
theorem spillR_bkt (I : FLImpl (GF := GF)) (γd : DBNames) (γ : GName) (W : WView) (txl : Loc)
    (txid : w64) (T : WTx) (ρ : DBState) (F : GMap Nat (List w8)) (K : Loc → Bool) (bl : Loc)
    (B : BRec) (hB : T.bs !! bl = some B) :
    spillR I γd γ W txl txid T ρ F K ⊢
      bktOwnX W bl B ∗ capsKN K B.ns ∗
      (∀ (B' : BRec) (K' : Loc → Bool),
        ⌜∀ l, K' l ≠ K l → (B.ns !! l).isSome ∨ (B'.ns !! l).isSome⌝ -∗
        bktOwnX W bl B' -∗ capsKN K' B'.ns -∗
        spillR I γd γ W txl txid (setB T bl B') ρ F K') := by
  unfold spillR ownWriteTxGX capsOwn
  iintro ⟨Hdb, ⟨Hrest, Hm, Hpm, Hbufs, Hbs⟩, Hv, Hcaps, Hgh, HF⟩
  icases (BigSepM.bigSepM_delete (M := GMap Loc) (Φ := fun bl B => bktOwnX (GF := GF) W bl B)
    (show Std.get? T.bs bl = some B from hB)).1 $$ Hbs with ⟨Hb, Hbs⟩
  icases (BigSepM.bigSepM_delete (M := GMap Loc)
    (Φ := fun _bl B => iprop([∗map] l ↦ r ∈ B.ns, if K l then iprop(emp) else capOwn (GF := GF) r))
    (show Std.get? T.bs bl = some B from hB)).1 $$ Hcaps with ⟨Hc, Hcaps⟩
  icases bkts_excl_b W (Std.delete T.bs bl) bl B $$ [Hbs Hb] with ⟨%hx1, Hbs, Hb⟩
  · iframe
  iframe Hb
  unfold capsKN
  iframe Hc
  iintro %B' %K' %hK Hb' Hc'
  icases bkts_excl_b W (Std.delete T.bs bl) bl B' $$ [Hbs Hb'] with ⟨%hx2, Hbs, Hb'⟩
  · iframe
  dsimp only [setB]
  have e : spillPages W { T with bs := <[bl := B']> T.bs } = spillPages W T := rfl
  rw [e]
  iframe Hdb Hrest Hm Hpm Hbufs Hv Hgh HF
  isplitl [Hb' Hbs]
  · iapply (BigSepM.bigSepM_insert_delete (M := GMap Loc) (Φ := fun bl B => bktOwnX (GF := GF) W bl B)).2
    iframe
  iapply (BigSepM.bigSepM_insert_delete (M := GMap Loc) (m := T.bs) (i := bl) (x := B')
    (Φ := fun _bl B => [∗map] l ↦ r ∈ B.ns, if K' l then iprop(emp) else capOwn (GF := GF) r)).2
  iframe Hc'
  iapply (BigSepM.bigSepM_mono (M := GMap Loc) ?_) $$ Hcaps
  intro b2 B2 hB2
  apply BigSepM.bigSepM_mono
  intro l r hr
  have e : K' l = K l := by
    apply Classical.byContradiction
    intro hne
    rcases hK l hne with h | h
    · have := hx1 b2 B2 l hB2 h; have hr' : B2.ns !! l = some r := hr
      rw [this] at hr'; cases hr'
    · have := hx2 b2 B2 l hB2 h; have hr' : B2.ns !! l = some r := hr
      rw [this] at hr'; cases hr'
  rw [e]

/-- A node's capacity, held unless `k`. -/
def capK (k : Bool) (r : NRec) : IProp GF := if k then iprop(emp) else capOwn r

/-- A node out of the spill state with its capacity (unless `K n`); back with any record and
capacity. -/
theorem spillR_upd (I : FLImpl (GF := GF)) (γd : DBNames) (γ : GName) (W : WView) (txl : Loc)
    (txid : w64) (T : WTx) (ρ : DBState) (F : GMap Nat (List w8)) (K : Loc → Bool) (bl : Loc)
    (B : BRec) (n : Loc) (r : NRec) (hB : T.bs !! bl = some B) (hn : B.ns !! n = some r) :
    spillR I γd γ W txl txid T ρ F K ⊢
      nodeOwnX W n r ∗ capK (K n) r ∗
      (∀ (r' : NRec) (k : Bool), nodeOwnX W n r' -∗ capK k r' -∗
        spillR I γd γ W txl txid (setB T bl (setN B n r')) ρ F
          (fun l => if l = n then k else K l)) := by
  iintro HR
  icases spillR_bkt I γd γ W txl txid T ρ F K bl B hB $$ HR with ⟨Hb, Hc, Hback⟩
  isimp only [bktOwnX] at Hb
  icases Hb with ⟨Hbv, Hib, Hnm, Hbm, Hpo, Hns⟩
  icases (BigSepM.bigSepM_delete (M := GMap Loc) (Φ := fun l r => nodeOwnX (GF := GF) W l r)
    (show Std.get? B.ns n = some r from hn)).1 $$ Hns with ⟨Hn, Hns⟩
  isimp only [capsKN] at Hc
  icases (BigSepM.bigSepM_delete (M := GMap Loc)
    (Φ := fun l r => if K l then iprop(emp) else capOwn (GF := GF) r)
    (show Std.get? B.ns n = some r from hn)).1 $$ Hc with ⟨Hcn, Hc⟩
  iframe Hn
  isplitl [Hcn]
  · unfold capK; iexact Hcn
  iintro %r' %k Hn' Hcn'
  have hK : ∀ l, (fun l => if l = n then k else K l) l ≠ K l →
      (B.ns !! l).isSome ∨ ((setN B n r').ns !! l).isSome := by
    intro l hl
    left
    by_cases h : l = n
    · subst h; rw [hn]; rfl
    · simp [h] at hl
  ihave Hb' : bktOwnX W bl (setN B n r') $$ [Hbv Hib Hnm Hbm Hpo Hns Hn']
  · unfold bktOwnX setN
    rw [show pageOwn W { B with ns := <[n := r']> B.ns } = pageOwn W B from rfl]
    iframe Hbv Hib Hnm Hbm Hpo
    iapply (BigSepM.bigSepM_insert_delete (M := GMap Loc) (m := B.ns) (i := n) (x := r')
      (Φ := fun l r => nodeOwnX (GF := GF) W l r)).2
    iframe
  ihave Hc' : capsKN (fun l => if l = n then k else K l) (setN B n r').ns $$ [Hcn' Hc]
  · unfold capsKN setN
    iapply (BigSepM.bigSepM_insert_delete (M := GMap Loc) (m := B.ns) (i := n) (x := r')
      (Φ := fun l r => if (fun l => if l = n then k else K l) l then iprop(emp) else capOwn (GF := GF) r)).2
    isplitl [Hcn']
    · unfold capK; simp only [ite_true]; iexact Hcn'
    iapply (BigSepM.bigSepM_mono (M := GMap Loc) ?_) $$ Hc
    intro l v hv
    have hl : l ≠ n := by
      intro e; subst e
      have : (Std.delete B.ns l : GMap Loc NRec) !! l = none := GMap.lookup_delete_eq _ _
      rw [show Std.get? (Std.delete B.ns l) l = (Std.delete B.ns l : GMap Loc NRec) !! l from rfl, this] at hv
      cases hv
    simp only [hl, ite_false]
    exact .rfl
  iapply Hback $$ %(setN B n r') %(fun l => if l = n then k else K l) %hK Hb' Hc'

end own

section spillg
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- The bucket `bl` changed in its nodes only, its live nodes ready: the spill's facts kept. -/
theorem spillG_setB (W : WView) (txl : Loc) (txid : w64) (T : WTx) (ρ : DBState)
    (F : GMap Nat (List w8)) (bl : Loc) (B B' : BRec) (hg : spillG (hG := hG) W txl txid T ρ F)
    (hB : T.bs !! bl = some B) (hbv : B'.bv = B.bv) (hbm : B'.bm = B.bm)
    (hlive : B'.bv.rootNode' = null ∨ ∃ S, liveNodesX B' S ∧
      ∀ l ∈ S, ∃ r, B'.ns !! l = some r ∧ derefOK bl r) :
    spillG (hG := hG) W txl txid (setB T bl B') ρ F := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, htx, hd, hu, hf, hr⟩ := hg
  have hlk : ∀ c, (setB T bl B').bs !! c = if c = bl then some B' else T.bs !! c := by
    intro c
    show (<[bl := B']> T.bs) !! c = _
    by_cases e : c = bl
    · subst e; rw [if_pos rfl]; exact GMap.lookup_insert _ _ _
    · rw [if_neg e]; exact GMap.lookup_insert_ne _ _ (Ne.symm e)
  have hdom : ∀ c, ((setB T bl B').bs !! c).isSome ↔ (T.bs !! c).isSome := by
    intro c; rw [hlk c]; by_cases e : c = bl
    · subst e; rw [if_pos rfl, hB]; rfl
    · rw [if_neg e]
  have hbm' : ∀ c C', (setB T bl B').bs !! c = some C' → ∃ C, T.bs !! c = some C ∧ C'.bm = C.bm := by
    intro c C' hc; rw [hlk c] at hc
    by_cases e : c = bl
    · subst e; rw [if_pos rfl] at hc; cases hc; exact ⟨B, hB, hbm⟩
    · rw [if_neg e] at hc; exact ⟨C', hc, rfl⟩
  have hbm'' : ∀ c C, T.bs !! c = some C → ∃ C', (setB T bl B').bs !! c = some C' ∧ C.bm = C'.bm := by
    intro c C hc
    by_cases e : c = bl
    · subst e; rw [hB] at hc; cases hc; exact ⟨B', by rw [hlk, if_pos rfl], hbm.symm⟩
    · exact ⟨C, by rw [hlk, if_neg e]; exact hc, rfl⟩
  obtain ⟨hr1, hr2, ⟨dep, hdep⟩, hr4⟩ := hr
  refine ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, ?_, hd, hu, hf, ?_⟩
  · intro c C hc; rw [hlk c] at hc
    by_cases e : c = bl
    · subst e; rw [if_pos rfl] at hc; cases hc; rw [hbv]; exact htx _ B hB
    · rw [if_neg e] at hc; exact htx c C hc
  refine ⟨(hdom _).2 hr1, fun c hc => ?_, ⟨dep, fun c C name c' hc hn => ?_⟩, fun c C hc => ?_⟩
  · exact bktReach_bmN T (setB T bl B') _ hbm' (fun c h => (hdom c).2 h) c (hr2 c ((hdom c).1 hc))
  · obtain ⟨C0, hC0, hb⟩ := hbm' c C hc
    exact hdep c C0 name c' hC0 (by rw [← hb]; exact hn)
  · rw [hlk c] at hc
    by_cases e : c = bl
    · subst e; rw [if_pos rfl] at hc; cases hc
      refine ⟨hlive, fun name c' hn => (hdom c').2 ((hr4 _ B hB).2 name c' (by rw [← hbm]; exact hn))⟩
    · rw [if_neg e] at hc
      refine ⟨(hr4 c C hc).1, fun name c' hn => (hdom c').2 ((hr4 c C hc).2 name c' hn)⟩

end spillg

end bbolt
end EtcdGrove
end Perennial
