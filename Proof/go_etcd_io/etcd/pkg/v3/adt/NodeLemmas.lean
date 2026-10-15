/-
Lemmas on the interval tree's representation (`Defs.lean`): the nodes split and combine by
fractions, and two parts of a subtree agree on its model (`ownNode_split`, `ownNode_combine`),
the same for the whole tree (`ownIvt_split'`, `ownIvt_combine`); the Go values' injectivity.
Lean-first.
-/
module

public import Proof.go_etcd_io.etcd.pkg.v3.adt.Defs

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace adt

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.pkg.v3.adt

section lemmas
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.pkg.v3.adt.Assumptions]

/-! ## The Go values -/

omit package_sem in
theorem colorW_inj {c1 c2 : RbColor} (h : colorW c1 = colorW c2) : c1 = c2 := by
  cases c1 <;> cases c2 <;> first | rfl | (exact absurd h (by decide))

omit package_sem in
include sem in
theorem affIvl_inj {b1 e1 b2 e2 : GoString} (h : affIvl b1 e1 = affIvl b2 e2) :
    b1 = b2 ∧ e1 = e2 := by
  unfold affIvl at h
  simp only [Interval.mk.injEq] at h
  obtain ⟨h1, h2⟩ := h
  simp only [GoInterface.ok.injEq, GoInterfaceOk.mk.injEq, true_and] at h1 h2
  exact ⟨go.intoVal_inj h1, go.intoVal_inj h2⟩

omit package_sem in
include sem in
/-- A node's `iv` value determines its entry. -/
theorem ivEntry_inj {z1 z2 : Entry}
    (h : ({ Ivl' := affIvl z1.1.1 z1.1.2, Val' := z1.2 } : IntervalValue) =
      { Ivl' := affIvl z2.1.1 z2.1.2, Val' := z2.2 }) : z1 = z2 := by
  simp only [IntervalValue.mk.injEq] at h
  obtain ⟨h1, h2⟩ := h
  obtain ⟨hb, he⟩ := affIvl_inj (sem := sem) h1
  exact Prod.ext (Prod.ext hb he) h2

theorem ownNode_node_open (s : Loc) (q : Qp) (p n : Loc) (c : RbColor) (l : RbT Entry)
    (e : Entry) (r : RbT Entry) :
    ownNode (GF := GF) s q p n (.node c l e r) ⊢ ∃ lp rp : Loc, ⌜n ≠ s ∧ n ≠ null⌝ ∗
      n.[intervalNode, go!"iv"] ↦{DFrac.own q}
        ({ Ivl' := affIvl e.1.1 e.1.2, Val' := e.2 } : IntervalValue) ∗
      n.[intervalNode, go!"max"] ↦{DFrac.own q} maxW (nodeMax l e r) ∗
      n.[intervalNode, go!"left"] ↦{DFrac.own q} lp ∗
      n.[intervalNode, go!"right"] ↦{DFrac.own q} rp ∗
      n.[intervalNode, go!"parent"] ↦{DFrac.own q} p ∗
      n.[intervalNode, go!"c"] ↦{DFrac.own q} colorW c ∗
      ownNode s q n lp l ∗ ownNode s q n rp r := by
  rw [ownNode_node]

theorem ownNode_node_close (s : Loc) (q : Qp) (p n : Loc) (c : RbColor) (l : RbT Entry)
    (e : Entry) (r : RbT Entry) :
    (∃ lp rp : Loc, ⌜n ≠ s ∧ n ≠ null⌝ ∗
      n.[intervalNode, go!"iv"] ↦{DFrac.own q}
        ({ Ivl' := affIvl e.1.1 e.1.2, Val' := e.2 } : IntervalValue) ∗
      n.[intervalNode, go!"max"] ↦{DFrac.own q} maxW (nodeMax l e r) ∗
      n.[intervalNode, go!"left"] ↦{DFrac.own q} lp ∗
      n.[intervalNode, go!"right"] ↦{DFrac.own q} rp ∗
      n.[intervalNode, go!"parent"] ↦{DFrac.own q} p ∗
      n.[intervalNode, go!"c"] ↦{DFrac.own q} colorW c ∗
      ownNode s q n lp l ∗ ownNode s q n rp r : IProp GF) ⊢ ownNode s q p n (.node c l e r) := by
  rw [ownNode_node]

theorem ownNode_leaf_open (s : Loc) (q : Qp) (p n : Loc) :
    ownNode (GF := GF) s q p n .leaf ⊢ ⌜n = s⌝ := by
  rw [ownNode_leaf]

theorem ownNode_leaf_close (s : Loc) (q : Qp) (p : Loc) :
    ⊢ ownNode (GF := GF) s q p s .leaf := by
  rw [ownNode_leaf]; exact pure_intro rfl

/-! ## Fractions -/

omit package_sem in
theorem tpq_split {A : Type} [TypedPointsto (GF := GF) A] (l : Loc) (v : A) (q1 q2 : Qp) :
    typedPointsto (GF := GF) l v (DFrac.own (q1 + q2)) ⊣⊢
      typedPointsto l v (DFrac.own q1) ∗ typedPointsto l v (DFrac.own q2) :=
  (fractional_of_dfractional (fun dq => typedPointsto (GF := GF) l v dq)).fractional q1 q2

theorem ownNode_split (s : Loc) (q1 q2 : Qp) : ∀ (p n : Loc) (T : RbT Entry),
    ownNode (GF := GF) s (q1 + q2) p n T ⊢ ownNode s q1 p n T ∗ ownNode s q2 p n T
  | p, n, .leaf => by
    rw [ownNode_leaf, ownNode_leaf, ownNode_leaf]
    iintro %h
    isplitl [] <;> ipureintro <;> exact h
  | p, n, .node c l e r => by
    rw [ownNode_node, ownNode_node, ownNode_node]
    iintro ⟨%lp, %rp, %Hn, Hiv, Hmx, Hl, Hr, Hp, Hc, Hnl, Hnr⟩
    icases (tpq_split _ _ q1 q2).1 $$ Hiv with ⟨Hiv1, Hiv2⟩
    icases (tpq_split _ _ q1 q2).1 $$ Hmx with ⟨Hmx1, Hmx2⟩
    icases (tpq_split _ _ q1 q2).1 $$ Hl with ⟨Hl1, Hl2⟩
    icases (tpq_split _ _ q1 q2).1 $$ Hr with ⟨Hr1, Hr2⟩
    icases (tpq_split _ _ q1 q2).1 $$ Hp with ⟨Hp1, Hp2⟩
    icases (tpq_split _ _ q1 q2).1 $$ Hc with ⟨Hc1, Hc2⟩
    icases ownNode_split s q1 q2 n lp l $$ Hnl with ⟨Hnl1, Hnl2⟩
    icases ownNode_split s q1 q2 n rp r $$ Hnr with ⟨Hnr1, Hnr2⟩
    isplitl [Hiv1 Hmx1 Hl1 Hr1 Hp1 Hc1 Hnl1 Hnr1]
    · iexists lp, rp; iframe; ipureintro; exact Hn
    · iexists lp, rp; iframe; ipureintro; exact Hn

theorem ownNode_combine (s : Loc) (q1 q2 : Qp) : ∀ (p n : Loc) (T1 T2 : RbT Entry),
    ownNode (GF := GF) s q1 p n T1 ∗ ownNode s q2 p n T2 ⊢
      ⌜T1 = T2⌝ ∗ ownNode s (q1 + q2) p n T1
  | p, n, .leaf, .leaf => by
    rw [ownNode_leaf, ownNode_leaf, ownNode_leaf]
    iintro ⟨%h, -⟩
    isplitl [] <;> ipureintro
    · rfl
    · exact h
  | p, n, .leaf, .node c l e r => by
    rw [ownNode_leaf, ownNode_node]
    iintro ⟨%h, %lp, %rp, %Hn, -⟩
    exact absurd h Hn.1
  | p, n, .node c l e r, .leaf => by
    rw [ownNode_leaf, ownNode_node]
    iintro ⟨⟨%lp, %rp, %Hn, -⟩, %h⟩
    exact absurd h Hn.1
  | p, n, .node c1 l1 e1 r1, .node c2 l2 e2 r2 => by
    rw [ownNode_node, ownNode_node, ownNode_node]
    iintro ⟨⟨%lp1, %rp1, %Hn, Hiv1, Hmx1, Hl1, Hr1, Hp1, Hc1, Hnl1, Hnr1⟩,
      ⟨%lp2, %rp2, -, Hiv2, Hmx2, Hl2, Hr2, Hp2, Hc2, Hnl2, Hnr2⟩⟩
    icombine Hl1 Hl2 gives %Hlp
    icombine Hr1 Hr2 gives %Hrp
    icombine Hiv1 Hiv2 gives %Hiv
    icombine Hc1 Hc2 gives %Hc
    subst Hlp Hrp
    obtain rfl := ivEntry_inj (sem := sem) Hiv
    obtain rfl := colorW_inj Hc
    icases ownNode_combine s q1 q2 n lp1 l1 l2 $$ [Hnl1 Hnl2] with ⟨%Hl, Hnl⟩
    · iframe
    icases ownNode_combine s q1 q2 n rp1 r1 r2 $$ [Hnr1 Hnr2] with ⟨%Hr, Hnr⟩
    · iframe
    subst Hl Hr
    isplitl []
    · ipureintro; rfl
    iexists lp1, rp1
    isplitl []
    · ipureintro; exact Hn
    isplitl [Hiv1 Hiv2]
    · iapply (tpq_split _ _ q1 q2).2; iframe
    isplitl [Hmx1 Hmx2]
    · iapply (tpq_split _ _ q1 q2).2; iframe
    isplitl [Hl1 Hl2]
    · iapply (tpq_split _ _ q1 q2).2; iframe
    isplitl [Hr1 Hr2]
    · iapply (tpq_split _ _ q1 q2).2; iframe
    isplitl [Hp1 Hp2]
    · iapply (tpq_split _ _ q1 q2).2; iframe
    isplitl [Hc1 Hc2]
    · iapply (tpq_split _ _ q1 q2).2; iframe
    iframe

theorem ownSentinel_split (s : Loc) (q1 q2 : Qp) :
    ownSentinel (GF := GF) s (q1 + q2) ⊣⊢ ownSentinel s q1 ∗ ownSentinel s q2 := by
  unfold ownSentinel
  constructor
  · iintro ⟨%v, H⟩
    icases (tpq_split _ _ q1 q2).1 $$ H with ⟨H1, H2⟩
    isplitl [H1]
    · iexists v; iexact H1
    · iexists v; iexact H2
  · iintro ⟨⟨%v1, H1⟩, ⟨%v2, H2⟩⟩
    icombine H1 H2 gives %Hv
    subst Hv
    iexists v1
    iapply (tpq_split _ _ q1 q2).2; iframe

/-- **The tree splits by fractions.** -/
theorem ownIvt_split' (t : Loc) (L : List Entry) (q1 q2 : Qp) :
    ownIvt (GF := GF) t L (q1 + q2) ⊢ ownIvt t L q1 ∗ ownIvt t L q2 := by
  unfold ownIvt
  iintro ⟨%tv, %T, Ht, Hs, Hn, %Hp⟩
  icases (tpq_split _ _ q1 q2).1 $$ Ht with ⟨Ht1, Ht2⟩
  icases (ownSentinel_split _ q1 q2).1 $$ Hs with ⟨Hs1, Hs2⟩
  icases ownNode_split _ q1 q2 _ _ T $$ Hn with ⟨Hn1, Hn2⟩
  isplitl [Ht1 Hs1 Hn1]
  · iexists tv, T; iframe; ipureintro; exact Hp
  · iexists tv, T; iframe; ipureintro; exact Hp

/-- **Two parts of the tree combine, and agree on the entries.** -/
theorem ownIvt_combine (t : Loc) (L1 L2 : List Entry) (q1 q2 : Qp) :
    ownIvt (GF := GF) t L1 q1 ∗ ownIvt t L2 q2 ⊢ ⌜L1 = L2⌝ ∗ ownIvt t L1 (q1 + q2) := by
  unfold ownIvt
  iintro ⟨⟨%tv1, %T1, Ht1, Hs1, Hn1, %Hp1⟩, ⟨%tv2, %T2, Ht2, Hs2, Hn2, %Hp2⟩⟩
  icombine Ht1 Ht2 gives %Htv
  subst Htv
  icases ownNode_combine _ q1 q2 _ _ T1 T2 $$ [Hn1 Hn2] with ⟨%HT, Hn⟩
  · iframe
  subst HT
  isplitl []
  · ipureintro; rw [← Hp1.1, ← Hp2.1]
  iexists tv1, T1
  isplitl [Ht1 Ht2]
  · iapply (tpq_split _ _ q1 q2).2; iframe
  isplitl [Hs1 Hs2]
  · iapply (ownSentinel_split _ q1 q2).2; iframe
  iframe
  ipureintro; exact Hp1

theorem ownIvt_not_null (t : Loc) (L : List Entry) (q : Qp) :
    ownIvt (GF := GF) t L q ⊢ ⌜t ≠ null⌝ := by
  unfold ownIvt
  iintro ⟨%tv, %T, Ht, -⟩
  iapply typedPointsto_not_null _ _ _ $$ Ht

/-- A node's `iv` (an entry's `IntervalValue`) as the fields the code loads: the interval's
begin and end and the value, given back by a wand. -/
theorem iv_open (l : Loc) (b e : GoString) (v : GoInterface) (dq : DFrac) :
    (l ↦{dq} ({ Ivl' := affIvl b e, Val' := v } : IntervalValue) : IProp GF) ⊢
      l.[IntervalValue, go!"Ivl"].[Interval, go!"Begin"] ↦{dq}
        interface.mkOk StringAffineComparable.ty #b ∗
      l.[IntervalValue, go!"Ivl"].[Interval, go!"End"] ↦{dq}
        interface.mkOk StringAffineComparable.ty #e ∗
      l.[IntervalValue, go!"Val"] ↦{dq} v ∗
      (l.[IntervalValue, go!"Ivl"].[Interval, go!"Begin"] ↦{dq}
          interface.mkOk StringAffineComparable.ty #b ∗
        l.[IntervalValue, go!"Ivl"].[Interval, go!"End"] ↦{dq}
          interface.mkOk StringAffineComparable.ty #e ∗
        l.[IntervalValue, go!"Val"] ↦{dq} v -∗
        l ↦{dq} ({ Ivl' := affIvl b e, Val' := v } : IntervalValue)) := by
  iintro H
  ihave %Hn := typedPointsto_not_null _ _ _ $$ H
  icases typedPointsto_split _ _ _ $$ H with H
  simp only [TypedPointsto.typedPointstoDef]
  iNamed H
  ihave %Hin := typedPointsto_not_null _ _ _ $$ Ivl
  icases ivl_split _ _ _ $$ Ivl with ⟨Hb, He, -⟩
  simp only [affIvl_Begin, affIvl_End]
  iframe Hb He Val
  iintro ⟨Hb, He, Hv⟩
  iapply typedPointsto_combine _ _ _ Hn
  simp only [TypedPointsto.typedPointstoDef]
  iframe Hv
  iapply ivl_combine _ _ _ Hin
  simp only [affIvl_Begin, affIvl_End]
  iframe Hb He

omit package_sem in
/-- A node's `iv` with its interval taken out (for `Interval.Compare`, given `&x.iv.Ivl`). -/
theorem iv_open_ivl (l : Loc) (b e : GoString) (v : GoInterface) (dq : DFrac) :
    (l ↦{dq} ({ Ivl' := affIvl b e, Val' := v } : IntervalValue) : IProp GF) ⊢
      l.[IntervalValue, go!"Ivl"] ↦{dq} affIvl b e ∗
      (l.[IntervalValue, go!"Ivl"] ↦{dq} affIvl b e -∗
        l ↦{dq} ({ Ivl' := affIvl b e, Val' := v } : IntervalValue)) := by
  iintro H
  ihave %Hn := typedPointsto_not_null _ _ _ $$ H
  icases typedPointsto_split _ _ _ $$ H with H
  simp only [TypedPointsto.typedPointstoDef]
  iNamed H
  iframe Ivl
  iintro Ivl
  iapply typedPointsto_combine _ _ _ Hn
  simp only [TypedPointsto.typedPointstoDef]
  iframe

/-! ## Reading the tree -/

omit package_sem in
/-- The tree struct as its fields. -/
theorem ivt_fields (t : Loc) (tv : intervalTree) (dq : DFrac) :
    (t ↦{dq} tv : IProp GF) ⊢
      t.[intervalTree, go!"root"] ↦{dq} tv.root' ∗ t.[intervalTree, go!"count"] ↦{dq} tv.count' ∗
      t.[intervalTree, go!"sentinel"] ↦{dq} tv.sentinel' ∗
      (t.[intervalTree, go!"root"] ↦{dq} tv.root' ∗ t.[intervalTree, go!"count"] ↦{dq} tv.count' ∗
        t.[intervalTree, go!"sentinel"] ↦{dq} tv.sentinel' -∗ t ↦{dq} tv) := by
  iintro Ht
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Ht
  iStructNamed Ht
  iframe root count sentinel
  iintro ⟨root, count, sentinel⟩
  iapply typedPointsto_combine _ _ _ Hnn
  simp only [TypedPointsto.typedPointstoDef]
  iframe

/-- **Reading the tree**: its fields and the nodes from the root, given back unchanged. -/
theorem ownIvt_read (t : Loc) (L : List Entry) (q : Qp) :
    ownIvt (GF := GF) t L q ⊢ ∃ (tv : intervalTree) (T : RbT Entry),
      t.[intervalTree, go!"root"] ↦{DFrac.own q} tv.root' ∗
      t.[intervalTree, go!"count"] ↦{DFrac.own q} tv.count' ∗
      t.[intervalTree, go!"sentinel"] ↦{DFrac.own q} tv.sentinel' ∗
      ownNode tv.sentinel' q tv.sentinel' tv.root' T ∗
      ⌜T.inorder = L ∧ RbOk T ∧ IvSorted L ∧ tv.count' = W64 L.length ∧ L.length < 2 ^ 63⌝ ∗
      (t.[intervalTree, go!"root"] ↦{DFrac.own q} tv.root' ∗
        t.[intervalTree, go!"count"] ↦{DFrac.own q} tv.count' ∗
        t.[intervalTree, go!"sentinel"] ↦{DFrac.own q} tv.sentinel' ∗
        ownNode tv.sentinel' q tv.sentinel' tv.root' T -∗ ownIvt t L q) := by
  unfold ownIvt
  iintro ⟨%tv, %T, Ht, Hs, Hn, %Hp⟩
  icases ivt_fields _ _ _ $$ Ht with ⟨Hr, Hc, Hsn, Hback⟩
  iexists tv, T
  iframe Hr Hc Hsn Hn
  isplitl []
  · ipureintro; exact Hp
  iintro ⟨Hr, Hc, Hsn, Hn⟩
  iexists tv, T
  iframe Hs Hn
  isplitl [Hr Hc Hsn Hback]
  · iapply Hback; iframe
  ipureintro; exact Hp

end lemmas

end adt
end EtcdGrove
end Perennial
