/-
Lemmas on the interval tree's representation (`Defs.lean`), generic in the key representation
`K`: the fields holding keys (`ivAt`, `maxAt`) opened to what the code loads, split and
combined by fractions, made read-only; the nodes split and combine by fractions, and two parts
of a subtree agree on its model (`ownNode_split`, `ownNode_combine`), the same for the whole
tree (`ownIvtK_split'`, `ownIvtK_combine`, and their string-affine forms); the Go values'
injectivity. Lean-first.
-/
module

public import Proof.go_etcd_io.etcd.pkg.v3.adt.Defs
public import Perennial.Golang.Theory.Map
public import Perennial.Ghost.GhostVar
public import Perennial.Ghost.GhostMap
public import Perennial.IrisLib.BI

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

/-- A points-to made read-only. -/
theorem tp_persist {V : Type} [TypedPointsto (GF := GF) V] (l : Loc) (v : V) (dq : DFrac) :
    (l ↦{dq} v : IProp GF) ⊢ |==> l ↦□ v :=
  (typedPointsto_dfractional (GF := GF) l v).dfractional_persist dq

/-! ## The key-holding fields -/

variable (K : KeyRep (GF := GF))

instance KeyRep.ivAt_persistent (l : Loc) (e : Entry) : Persistent (K.ivAt l .discard e) := by
  unfold KeyRep.ivAt; infer_instance

instance KeyRep.maxAt_persistent (l : Loc) (m : GoString) : Persistent (K.maxAt l .discard m) := by
  unfold KeyRep.maxAt; infer_instance

theorem KeyRep.ivAt_persist (l : Loc) (dq : DFrac) (e : Entry) :
    K.ivAt l dq e ⊢ |==> K.ivAt l .discard e := by
  unfold KeyRep.ivAt
  iintro ⟨%vb, %ve, H, #Hb, #He⟩
  imod tp_persist _ _ _ $$ H with H
  imodintro
  iexists vb, ve
  iframe ∗ #

theorem KeyRep.maxAt_persist (l : Loc) (dq : DFrac) (m : GoString) :
    K.maxAt l dq m ⊢ |==> K.maxAt l .discard m := by
  unfold KeyRep.maxAt
  iintro ⟨%vm, H, #Hm⟩
  imod tp_persist _ _ _ $$ H with H
  imodintro
  iexists vm
  iframe ∗ #

theorem KeyRep.ivAt_not_null (l : Loc) (dq : DFrac) (e : Entry) : K.ivAt l dq e ⊢ ⌜l ≠ null⌝ := by
  unfold KeyRep.ivAt
  iintro ⟨%vb, %ve, H, -, -⟩
  iapply typedPointsto_not_null _ _ _ $$ H

theorem KeyRep.ivAt_split (l : Loc) (q1 q2 : Qp) (e : Entry) :
    K.ivAt l (DFrac.own (q1 + q2)) e ⊢ K.ivAt l (DFrac.own q1) e ∗ K.ivAt l (DFrac.own q2) e := by
  unfold KeyRep.ivAt
  iintro ⟨%vb, %ve, H, #Hb, #He⟩
  icases (typedPointsto_frac_add _ _ q1 q2).1 $$ H with ⟨H1, H2⟩
  isplitl [H1]
  · iexists vb, ve; iframe ∗ #
  · iexists vb, ve; iframe ∗ #

theorem KeyRep.maxAt_split (l : Loc) (q1 q2 : Qp) (m : GoString) :
    K.maxAt l (DFrac.own (q1 + q2)) m ⊢ K.maxAt l (DFrac.own q1) m ∗ K.maxAt l (DFrac.own q2) m := by
  unfold KeyRep.maxAt
  iintro ⟨%vm, H, #Hm⟩
  icases (typedPointsto_frac_add _ _ q1 q2).1 $$ H with ⟨H1, H2⟩
  isplitl [H1]
  · iexists vm; iframe ∗ #
  · iexists vm; iframe ∗ #

/-- Two parts of a node's `iv` agree on the entry. -/
theorem KeyRep.ivAt_combine (l : Loc) (q1 q2 : Qp) (e1 e2 : Entry) :
    K.ivAt l (DFrac.own q1) e1 ∗ K.ivAt l (DFrac.own q2) e2 ⊢
      ⌜e1 = e2⌝ ∗ K.ivAt l (DFrac.own (q1 + q2)) e1 := by
  unfold KeyRep.ivAt
  iintro ⟨⟨%vb1, %ve1, H1, #Hb1, #He1⟩, ⟨%vb2, %ve2, H2, #Hb2, #He2⟩⟩
  icombine H1 H2 gives %Hv
  simp only [IntervalValue.mk.injEq] at Hv
  obtain ⟨hivl, hval⟩ := Hv
  obtain ⟨rfl, rfl⟩ := K.ivl_inj hivl
  ihave %hb := K.keyAt_agree .discard .discard vb1 e1.1.1 e2.1.1 $$ [Hb1 Hb2]
  · iframe ∗ #
  ihave %he := K.keyAt_agree .discard .discard ve1 e1.1.2 e2.1.2 $$ [He1 He2]
  · iframe ∗ #
  have heq : e1 = e2 := Prod.ext (Prod.ext hb he) hval
  subst heq
  isplitl []
  · ipureintro; rfl
  iexists vb1, ve1
  isplitl [H1 H2]
  · iapply (typedPointsto_frac_add _ _ q1 q2).2; iframe
  iframe ∗ #

/-- Two parts of a node's `max` agree on the key. -/
theorem KeyRep.maxAt_combine (l : Loc) (q1 q2 : Qp) (m1 m2 : GoString) :
    K.maxAt l (DFrac.own q1) m1 ∗ K.maxAt l (DFrac.own q2) m2 ⊢
      ⌜m1 = m2⌝ ∗ K.maxAt l (DFrac.own (q1 + q2)) m1 := by
  unfold KeyRep.maxAt
  iintro ⟨⟨%vm1, H1, #Hm1⟩, ⟨%vm2, H2, #Hm2⟩⟩
  icombine H1 H2 gives %Hv
  simp only [GoInterface.ok.injEq, GoInterfaceOk.mk.injEq, true_and] at Hv
  subst Hv
  ihave %hm := K.keyAt_agree .discard .discard vm1 m1 m2 $$ [Hm1 Hm2]
  · iframe ∗ #
  isplitl []
  · ipureintro; exact hm
  iexists vm1
  isplitl [H1 H2]
  · iapply (typedPointsto_frac_add _ _ q1 q2).2; iframe ∗ #
  iframe ∗ #

/-- A node's `iv` (an entry's `IntervalValue`) as the fields the code loads: the interval's
begin and end (values holding the entry's keys, read-only) and the value, given back by a
wand. -/
theorem KeyRep.ivAt_open (l : Loc) (dq : DFrac) (e : Entry) :
    K.ivAt l dq e ⊢ ∃ vb ve : val,
      l.[IntervalValue, go!"Ivl"].[Interval, go!"Begin"] ↦{dq} interface.mkOk K.ty vb ∗
      l.[IntervalValue, go!"Ivl"].[Interval, go!"End"] ↦{dq} interface.mkOk K.ty ve ∗
      l.[IntervalValue, go!"Val"] ↦{dq} e.2 ∗
      K.keyAt .discard vb e.1.1 ∗ K.keyAt .discard ve e.1.2 ∗
      (l.[IntervalValue, go!"Ivl"].[Interval, go!"Begin"] ↦{dq} interface.mkOk K.ty vb ∗
        l.[IntervalValue, go!"Ivl"].[Interval, go!"End"] ↦{dq} interface.mkOk K.ty ve ∗
        l.[IntervalValue, go!"Val"] ↦{dq} e.2 -∗ K.ivAt l dq e) := by
  unfold KeyRep.ivAt
  iintro ⟨%vb, %ve, H, #Hb, #He⟩
  ihave %Hn := typedPointsto_not_null _ _ _ $$ H
  icases typedPointsto_split _ _ _ $$ H with H
  simp only [TypedPointsto.typedPointstoDef]
  iNamed H
  ihave %Hin := typedPointsto_not_null _ _ _ $$ Ivl
  icases ivl_split _ _ _ $$ Ivl with ⟨Hb', He', -⟩
  simp only [KeyRep.ivl_Begin, KeyRep.ivl_End]
  iexists vb, ve
  iframe Hb' He' Val
  iframe #
  iintro ⟨Hb', He', Hv⟩
  iexists vb, ve
  iframe ∗ #
  iapply typedPointsto_combine _ _ _ Hn
  simp only [TypedPointsto.typedPointstoDef]
  iframe Hv
  iapply ivl_combine _ _ _ Hin
  simp only [KeyRep.ivl_Begin, KeyRep.ivl_End]
  iframe Hb' He'

/-- A node's `iv` with its interval taken out (for `Interval.Compare`, given `&x.iv.Ivl`). -/
theorem KeyRep.ivAt_open_ivl (l : Loc) (dq : DFrac) (e : Entry) :
    K.ivAt l dq e ⊢ ∃ vb ve : val,
      l.[IntervalValue, go!"Ivl"] ↦{dq} K.ivl vb ve ∗
      K.keyAt .discard vb e.1.1 ∗ K.keyAt .discard ve e.1.2 ∗
      (l.[IntervalValue, go!"Ivl"] ↦{dq} K.ivl vb ve -∗ K.ivAt l dq e) := by
  unfold KeyRep.ivAt
  iintro ⟨%vb, %ve, H, #Hb, #He⟩
  ihave %Hn := typedPointsto_not_null _ _ _ $$ H
  icases typedPointsto_split _ _ _ $$ H with H
  simp only [TypedPointsto.typedPointstoDef]
  iNamed H
  iexists vb, ve
  iframe ∗ #
  iintro Ivl
  iexists vb, ve
  iframe ∗ #
  iapply typedPointsto_combine _ _ _ Hn
  simp only [TypedPointsto.typedPointstoDef]
  iframe ∗ #

/-- A node's `iv` as its interval (whole) and its value, given back by a wand (`Union`'s
`Insert(n.Ivl, n.Val)`). -/
theorem KeyRep.ivAt_open_ivl_val (l : Loc) (dq : DFrac) (e : Entry) :
    K.ivAt l dq e ⊢ ∃ vb ve : val,
      l.[IntervalValue, go!"Ivl"] ↦{dq} K.ivl vb ve ∗ l.[IntervalValue, go!"Val"] ↦{dq} e.2 ∗
      K.keyAt .discard vb e.1.1 ∗ K.keyAt .discard ve e.1.2 ∗
      (l.[IntervalValue, go!"Ivl"] ↦{dq} K.ivl vb ve ∗ l.[IntervalValue, go!"Val"] ↦{dq} e.2 -∗
        K.ivAt l dq e) := by
  unfold KeyRep.ivAt
  iintro ⟨%vb, %ve, H, #Hb, #He⟩
  ihave %Hn := typedPointsto_not_null _ _ _ $$ H
  icases typedPointsto_split _ _ _ $$ H with H
  simp only [TypedPointsto.typedPointstoDef]
  iNamed H
  iexists vb, ve
  iframe Ivl Val
  iframe #
  iintro ⟨Ivl, Val⟩
  iexists vb, ve
  iframe Hb He
  iapply typedPointsto_combine _ _ _ Hn
  simp only [TypedPointsto.typedPointstoDef]
  iframe

/-- A node's `iv` as the `IntervalValue` points-to the code loads and stores whole
(`Delete`'s `z.iv = y.iv`), with the values holding the keys. -/
theorem KeyRep.ivAt_open_raw (l : Loc) (dq : DFrac) (e : Entry) :
    K.ivAt l dq e ⊢ ∃ vb ve : val,
      l ↦{dq} ({ Ivl' := K.ivl vb ve, Val' := e.2 } : IntervalValue) ∗
      K.keyAt .discard vb e.1.1 ∗ K.keyAt .discard ve e.1.2 := by
  unfold KeyRep.ivAt
  iintro ⟨%vb, %ve, H, Hb, He⟩
  iexists vb, ve
  iframe

/-- A node's `iv` from its fields (`createIntervalNode`, `Delete`'s copy). -/
theorem KeyRep.ivAt_intro (l : Loc) (dq : DFrac) (e : Entry) (vb ve : val) :
    l ↦{dq} ({ Ivl' := K.ivl vb ve, Val' := e.2 } : IntervalValue) ∗
      K.keyAt .discard vb e.1.1 ∗ K.keyAt .discard ve e.1.2 ⊢ K.ivAt l dq e := by
  unfold KeyRep.ivAt
  iintro ⟨H, Hb, He⟩
  iexists vb, ve
  iframe ∗ #

/-- A node's `max` as the `Comparable` the code loads (a value holding the key, read-only),
given back by a wand (for a new value holding the same key, `maxAt_intro`). -/
theorem KeyRep.maxAt_open (l : Loc) (dq : DFrac) (m : GoString) :
    K.maxAt l dq m ⊢ ∃ vm : val, l ↦{dq} interface.mkOk K.ty vm ∗ K.keyAt .discard vm m := by
  unfold KeyRep.maxAt
  iintro ⟨%vm, H, #Hm⟩
  iexists vm
  iframe ∗ #

theorem KeyRep.maxAt_intro (l : Loc) (dq : DFrac) (m : GoString) (vm : val) :
    l ↦{dq} interface.mkOk K.ty vm ∗ K.keyAt .discard vm m ⊢ K.maxAt l dq m := by
  unfold KeyRep.maxAt
  iintro ⟨H, Hm⟩
  iexists vm
  iframe ∗ #

/-! ## The nodes -/

theorem ownNode_node_open (s : Loc) (dq : DFrac) (p n : Loc) (c : RbColor) (l : RbT Entry)
    (e : Entry) (r : RbT Entry) :
    ownNode K s dq p n (.node c l e r) ⊢ ∃ lp rp : Loc, ⌜n ≠ s ∧ n ≠ null⌝ ∗
      K.ivAt n.[intervalNode, go!"iv"] dq e ∗
      K.maxAt n.[intervalNode, go!"max"] dq (nodeMax l e r) ∗
      n.[intervalNode, go!"left"] ↦{dq} lp ∗
      n.[intervalNode, go!"right"] ↦{dq} rp ∗
      n.[intervalNode, go!"parent"] ↦{dq} p ∗
      n.[intervalNode, go!"c"] ↦{dq} colorW c ∗
      ownNode K s dq n lp l ∗ ownNode K s dq n rp r := by
  rw [ownNode_node]

theorem ownNode_node_close (s : Loc) (dq : DFrac) (p n : Loc) (c : RbColor) (l : RbT Entry)
    (e : Entry) (r : RbT Entry) :
    (∃ lp rp : Loc, ⌜n ≠ s ∧ n ≠ null⌝ ∗
      K.ivAt n.[intervalNode, go!"iv"] dq e ∗
      K.maxAt n.[intervalNode, go!"max"] dq (nodeMax l e r) ∗
      n.[intervalNode, go!"left"] ↦{dq} lp ∗
      n.[intervalNode, go!"right"] ↦{dq} rp ∗
      n.[intervalNode, go!"parent"] ↦{dq} p ∗
      n.[intervalNode, go!"c"] ↦{dq} colorW c ∗
      ownNode K s dq n lp l ∗ ownNode K s dq n rp r : IProp GF) ⊢
      ownNode K s dq p n (.node c l e r) := by
  rw [ownNode_node]

theorem ownNode_leaf_open (s : Loc) (dq : DFrac) (p n : Loc) :
    ownNode K s dq p n .leaf ⊢ ⌜n = s⌝ := by
  rw [ownNode_leaf]

theorem ownNode_leaf_close (s : Loc) (dq : DFrac) (p : Loc) :
    ⊢ ownNode K s dq p s .leaf := by
  rw [ownNode_leaf]; exact pure_intro rfl

/-- A node is not the sentinel, nor `nil`. -/
theorem ownNode_node_ne (s : Loc) (dq : DFrac) (p n : Loc) (c : RbColor) (l : RbT Entry)
    (e : Entry) (r : RbT Entry) : ownNode K s dq p n (.node c l e r) ⊢ ⌜n ≠ s ∧ n ≠ null⌝ := by
  iintro H
  icases ownNode_node_open _ _ _ _ _ _ _ _ _ $$ H with ⟨%lp, %rp, %Hn, -⟩
  ipureintro; exact Hn

/-! ## Fractions and persistence -/

theorem ownNode_split (s : Loc) (q1 q2 : Qp) : ∀ (p n : Loc) (T : RbT Entry),
    ownNode K s (DFrac.own (q1 + q2)) p n T ⊢
      ownNode K s (DFrac.own q1) p n T ∗ ownNode K s (DFrac.own q2) p n T
  | p, n, .leaf => by
    rw [ownNode_leaf, ownNode_leaf, ownNode_leaf]
    iintro %h
    isplitl [] <;> ipureintro <;> exact h
  | p, n, .node c l e r => by
    rw [ownNode_node, ownNode_node, ownNode_node]
    iintro ⟨%lp, %rp, %Hn, Hiv, Hmx, Hl, Hr, Hp, Hc, Hnl, Hnr⟩
    icases K.ivAt_split _ q1 q2 _ $$ Hiv with ⟨Hiv1, Hiv2⟩
    icases K.maxAt_split _ q1 q2 _ $$ Hmx with ⟨Hmx1, Hmx2⟩
    icases (typedPointsto_frac_add _ _ q1 q2).1 $$ Hl with ⟨Hl1, Hl2⟩
    icases (typedPointsto_frac_add _ _ q1 q2).1 $$ Hr with ⟨Hr1, Hr2⟩
    icases (typedPointsto_frac_add _ _ q1 q2).1 $$ Hp with ⟨Hp1, Hp2⟩
    icases (typedPointsto_frac_add _ _ q1 q2).1 $$ Hc with ⟨Hc1, Hc2⟩
    icases ownNode_split s q1 q2 n lp l $$ Hnl with ⟨Hnl1, Hnl2⟩
    icases ownNode_split s q1 q2 n rp r $$ Hnr with ⟨Hnr1, Hnr2⟩
    isplitl [Hiv1 Hmx1 Hl1 Hr1 Hp1 Hc1 Hnl1 Hnr1]
    · iexists lp, rp; iframe; ipureintro; exact Hn
    · iexists lp, rp; iframe; ipureintro; exact Hn

theorem ownNode_combine (s : Loc) (q1 q2 : Qp) : ∀ (p n : Loc) (T1 T2 : RbT Entry),
    ownNode K s (DFrac.own q1) p n T1 ∗ ownNode K s (DFrac.own q2) p n T2 ⊢
      ⌜T1 = T2⌝ ∗ ownNode K s (DFrac.own (q1 + q2)) p n T1
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
    icombine Hc1 Hc2 gives %Hc
    subst Hlp Hrp
    icases K.ivAt_combine _ q1 q2 e1 e2 $$ [Hiv1 Hiv2] with ⟨%He, Hiv⟩
    · iframe ∗ #
    subst He
    obtain rfl := colorW_inj Hc
    icases ownNode_combine s q1 q2 n lp1 l1 l2 $$ [Hnl1 Hnl2] with ⟨%Hl, Hnl⟩
    · iframe ∗ #
    icases ownNode_combine s q1 q2 n rp1 r1 r2 $$ [Hnr1 Hnr2] with ⟨%Hr, Hnr⟩
    · iframe ∗ #
    subst Hl Hr
    icases K.maxAt_combine _ q1 q2 _ _ $$ [Hmx1 Hmx2] with ⟨-, Hmx⟩
    · iframe ∗ #
    isplitl []
    · ipureintro; rfl
    iexists lp1, rp1
    isplitl []
    · ipureintro; exact Hn
    iframe Hiv Hmx
    isplitl [Hl1 Hl2]
    · iapply (typedPointsto_frac_add _ _ q1 q2).2; iframe ∗ #
    isplitl [Hr1 Hr2]
    · iapply (typedPointsto_frac_add _ _ q1 q2).2; iframe ∗ #
    isplitl [Hp1 Hp2]
    · iapply (typedPointsto_frac_add _ _ q1 q2).2; iframe ∗ #
    isplitl [Hc1 Hc2]
    · iapply (typedPointsto_frac_add _ _ q1 q2).2; iframe ∗ #
    iframe ∗ #

set_option synthInstance.maxSize 512 in
theorem ownNode_persistent (s p n : Loc) :
    ∀ T : RbT Entry, Persistent (ownNode K s .discard p n T)
  | .leaf => by rw [ownNode_leaf]; infer_instance
  | .node c l e r => by
    rw [ownNode_node]
    have hl : ∀ lp, Persistent (ownNode K s .discard n lp l) :=
      fun lp => ownNode_persistent s n lp l
    have hr : ∀ rp, Persistent (ownNode K s .discard n rp r) :=
      fun rp => ownNode_persistent s n rp r
    infer_instance

instance ownNode_persistent_inst (s p n : Loc) (T : RbT Entry) :
    Persistent (ownNode K s .discard p n T) := ownNode_persistent K s p n T

/-- A subtree made read-only. -/
theorem ownNode_persist (s : Loc) : ∀ (T : RbT Entry) (p n : Loc),
    ownNode K s (DFrac.own 1) p n T ⊢ |==> ownNode K s .discard p n T
  | .leaf, p, n => by rw [ownNode_leaf, ownNode_leaf]; iintro H; imodintro; iexact H
  | .node c l e r, p, n => by
    rw [ownNode_node, ownNode_node]
    iintro ⟨%lp, %rp, %Hn, Hiv, Hmx, Hl, Hr, Hp, Hc, HL, HR⟩
    imod K.ivAt_persist _ _ _ $$ Hiv with Hiv
    imod K.maxAt_persist _ _ _ $$ Hmx with Hmx
    imod tp_persist _ _ _ $$ Hl with Hl
    imod tp_persist _ _ _ $$ Hr with Hr
    imod tp_persist _ _ _ $$ Hp with Hp
    imod tp_persist _ _ _ $$ Hc with Hc
    imod ownNode_persist s l n lp $$ HL with HL
    imod ownNode_persist s r n rp $$ HR with HR
    imodintro
    iexists lp, rp
    iframe ∗ #
    ipureintro; exact Hn

omit K in
theorem ownSentinel_split (s : Loc) (q1 q2 : Qp) :
    ownSentinel (GF := GF) s (DFrac.own (q1 + q2)) ⊣⊢
      ownSentinel s (DFrac.own q1) ∗ ownSentinel s (DFrac.own q2) := by
  unfold ownSentinel
  constructor
  · iintro ⟨%v, H⟩
    icases (typedPointsto_frac_add _ _ q1 q2).1 $$ H with ⟨H1, H2⟩
    isplitl [H1]
    · iexists v; iexact H1
    · iexists v; iexact H2
  · iintro ⟨⟨%v1, H1⟩, ⟨%v2, H2⟩⟩
    icombine H1 H2 gives %Hv
    subst Hv
    iexists v1
    iapply (typedPointsto_frac_add _ _ q1 q2).2; iframe ∗ #

omit K in
instance ownSentinel_persistent (s : Loc) : Persistent (ownSentinel (GF := GF) s .discard) := by
  unfold ownSentinel; infer_instance

/-! ## The tree -/

/-- **The tree splits by fractions.** -/
theorem ownIvtK_split' (t : Loc) (L : List Entry) (q1 q2 : Qp) :
    ownIvtK K t L (DFrac.own (q1 + q2)) ⊢
      ownIvtK K t L (DFrac.own q1) ∗ ownIvtK K t L (DFrac.own q2) := by
  unfold ownIvtK
  iintro ⟨%tv, %T, Ht, Hs, Hn, %Hp⟩
  icases (typedPointsto_frac_add _ _ q1 q2).1 $$ Ht with ⟨Ht1, Ht2⟩
  icases (ownSentinel_split _ q1 q2).1 $$ Hs with ⟨Hs1, Hs2⟩
  icases ownNode_split K _ q1 q2 _ _ T $$ Hn with ⟨Hn1, Hn2⟩
  isplitl [Ht1 Hs1 Hn1]
  · iexists tv, T; iframe; ipureintro; exact Hp
  · iexists tv, T; iframe; ipureintro; exact Hp

/-- **Two parts of the tree combine, and agree on the entries.** -/
theorem ownIvtK_combine (t : Loc) (L1 L2 : List Entry) (q1 q2 : Qp) :
    ownIvtK K t L1 (DFrac.own q1) ∗ ownIvtK K t L2 (DFrac.own q2) ⊢
      ⌜L1 = L2⌝ ∗ ownIvtK K t L1 (DFrac.own (q1 + q2)) := by
  unfold ownIvtK
  iintro ⟨⟨%tv1, %T1, Ht1, Hs1, Hn1, %Hp1⟩, ⟨%tv2, %T2, Ht2, Hs2, Hn2, %Hp2⟩⟩
  icombine Ht1 Ht2 gives %Htv
  subst Htv
  icases ownNode_combine K _ q1 q2 _ _ T1 T2 $$ [Hn1 Hn2] with ⟨%HT, Hn⟩
  · iframe ∗ #
  subst HT
  isplitl []
  · ipureintro; rw [← Hp1.1, ← Hp2.1]
  iexists tv1, T1
  isplitl [Ht1 Ht2]
  · iapply (typedPointsto_frac_add _ _ q1 q2).2; iframe ∗ #
  isplitl [Hs1 Hs2]
  · iapply (ownSentinel_split _ q1 q2).2; iframe ∗ #
  iframe ∗ #
  ipureintro; exact Hp1

instance ownIvtK_persistent (t : Loc) (L : List Entry) : Persistent (ownIvtK K t L .discard) := by
  unfold ownIvtK; infer_instance

/-- A built tree made read-only. -/
theorem ownIvtK_persist (t : Loc) (L : List Entry) :
    ownIvtK K t L (DFrac.own 1) ⊢ |==> ownIvtK K t L .discard := by
  unfold ownIvtK ownSentinel
  iintro ⟨%tv, %T, Ht, ⟨%sv, Hs⟩, Hn, %H⟩
  imod tp_persist _ _ _ $$ Ht with Ht
  imod tp_persist _ _ _ $$ Hs with Hs
  imod ownNode_persist K _ _ _ _ $$ Hn with Hn
  imodintro
  iexists tv, T
  iframe ∗ #
  ipureintro; exact H

/-- The entries are in the tree's order. -/
theorem ownIvtK_sorted (t : Loc) (L : List Entry) (dq : DFrac) :
    ownIvtK K t L dq ⊢ ⌜IvSorted L⌝ := by
  unfold ownIvtK
  iintro ⟨%tv, %T, -, -, -, %H⟩
  ipureintro; exact H.2.2.1

theorem ownIvtK_not_null (t : Loc) (L : List Entry) (dq : DFrac) :
    ownIvtK K t L dq ⊢ ⌜t ≠ null⌝ := by
  unfold ownIvtK
  iintro ⟨%tv, %T, Ht, -⟩
  iapply typedPointsto_not_null _ _ _ $$ Ht

omit K in
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
  iframe ∗ #

/-- **Reading the tree**: its fields and the nodes from the root, given back unchanged. -/
theorem ownIvtK_read (t : Loc) (L : List Entry) (dq : DFrac) :
    ownIvtK K t L dq ⊢ ∃ (tv : intervalTree) (T : RbT Entry),
      t.[intervalTree, go!"root"] ↦{dq} tv.root' ∗
      t.[intervalTree, go!"count"] ↦{dq} tv.count' ∗
      t.[intervalTree, go!"sentinel"] ↦{dq} tv.sentinel' ∗
      ownNode K tv.sentinel' dq tv.sentinel' tv.root' T ∗
      ⌜T.inorder = L ∧ RbOk T ∧ IvSorted L ∧ tv.count' = W64 L.length ∧ L.length < 2 ^ 63⌝ ∗
      (t.[intervalTree, go!"root"] ↦{dq} tv.root' ∗
        t.[intervalTree, go!"count"] ↦{dq} tv.count' ∗
        t.[intervalTree, go!"sentinel"] ↦{dq} tv.sentinel' ∗
        ownNode K tv.sentinel' dq tv.sentinel' tv.root' T -∗ ownIvtK K t L dq) := by
  unfold ownIvtK
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
  · iapply Hback; iframe ∗ #
  ipureintro; exact Hp

/-! ## The string-affine tree -/

omit K in
theorem ownIvt_split' (t : Loc) (L : List Entry) (q1 q2 : Qp) :
    ownIvt (GF := GF) t L (q1 + q2) ⊢ ownIvt t L q1 ∗ ownIvt t L q2 :=
  ownIvtK_split' strKey t L q1 q2

omit K in
theorem ownIvt_combine (t : Loc) (L1 L2 : List Entry) (q1 q2 : Qp) :
    ownIvt (GF := GF) t L1 q1 ∗ ownIvt t L2 q2 ⊢ ⌜L1 = L2⌝ ∗ ownIvt t L1 (q1 + q2) :=
  ownIvtK_combine strKey t L1 L2 q1 q2

omit K in
theorem ownIvt_not_null (t : Loc) (L : List Entry) (q : Qp) :
    ownIvt (GF := GF) t L q ⊢ ⌜t ≠ null⌝ :=
  ownIvtK_not_null strKey t L (DFrac.own q)

omit K in
/-- The string-affine node's `iv` is the entry's `IntervalValue` (`strKey` holds no resource). -/
theorem strKey_ivAt (l : Loc) (dq : DFrac) (e : Entry) :
    (strKey (GF := GF)).ivAt l dq e ⊣⊢
      l ↦{dq} ({ Ivl' := affIvl e.1.1 e.1.2, Val' := e.2 } : IntervalValue) := by
  unfold KeyRep.ivAt
  rw [affIvl_eq (GF := GF)]
  constructor
  · simp only [strKey_keyAt]
    iintro ⟨%vb, %ve, H, %Hb, %He⟩
    subst Hb He
    iexact H
  · simp only [strKey_keyAt]
    iintro H
    iexists #e.1.1, #e.1.2
    iframe
    isplitl [] <;> ipureintro <;> rfl

end lemmas

end adt
end EtcdGrove
end Perennial
