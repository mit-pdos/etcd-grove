/-
The interval tree with a hole (`Insert`'s and the fixups' view of it, at the fraction `1`):
`ownCtx t s C n p mh`, the nodes on the path from the tree's root (the `root` field of the
tree struct `t`) down to the hole at `n` (child of `p`), the context `C` of `TreeInsert.lean`,
each node with its other subtree (`ownNode`); the nodes' `max` fields are those of the tree
whose hole's subtree has the max `mh` (`nodeMaxO`), so that a write to the hole's `max` makes
its parent inconsistent until `updateMax` walks up (its spec is over this predicate). With the
hole's subtree's max, it is the whole tree (`ownCtx_plug`). And the pieces the helpers read:
a child's `max` (`childMax`), a node's colour (`colorAt`, `color(sentinel)`). Lean-first.
-/
module

public import Proof.go_etcd_io.etcd.pkg.v3.adt.NodeLemmas
public import Proof.go_etcd_io.etcd.pkg.v3.adt.TreeInsert

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace adt

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.pkg.v3.adt

section ctx
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.pkg.v3.adt.Assumptions]

/-- The path from the root to the hole at `n` (child of `p`) of the tree at `t` (whose sentinel
is `s`), in the context `C`, the hole's subtree's max being `mh`: at the top, the tree's `root`
field (and `p` the sentinel); a frame, the parent node `p` (not the sentinel) with its fields,
its child pointer at `n`, its `max` as `updateMax` computes it from `mh`, its other subtree,
and its own context. -/
def ownCtx (t s : Loc) : RbCtx Entry → Loc → Loc → Option GoString → IProp GF
  | .top, n, p, _ => iprop(⌜p = s⌝ ∗ t.[intervalTree, go!"root"] ↦ n)
  | .inL c C e r, n, p, mh => iprop(∃ pp rp : Loc, ⌜p ≠ s ∧ p ≠ null⌝ ∗
      p.[intervalNode, go!"iv"] ↦
        ({ Ivl' := affIvl e.1.1 e.1.2, Val' := e.2 } : IntervalValue) ∗
      p.[intervalNode, go!"max"] ↦ maxW (nodeMaxO mh e r.maxEnd) ∗
      p.[intervalNode, go!"left"] ↦ n ∗
      p.[intervalNode, go!"right"] ↦ rp ∗
      p.[intervalNode, go!"parent"] ↦ pp ∗
      p.[intervalNode, go!"c"] ↦ colorW c ∗
      ownNode s 1 p rp r ∗ ownCtx t s C p pp (some (nodeMaxO mh e r.maxEnd)))
  | .inR c l e C, n, p, mh => iprop(∃ pp lp : Loc, ⌜p ≠ s ∧ p ≠ null⌝ ∗
      p.[intervalNode, go!"iv"] ↦
        ({ Ivl' := affIvl e.1.1 e.1.2, Val' := e.2 } : IntervalValue) ∗
      p.[intervalNode, go!"max"] ↦ maxW (nodeMaxO l.maxEnd e mh) ∗
      p.[intervalNode, go!"left"] ↦ lp ∗
      p.[intervalNode, go!"right"] ↦ n ∗
      p.[intervalNode, go!"parent"] ↦ pp ∗
      p.[intervalNode, go!"c"] ↦ colorW c ∗
      ownNode s 1 p lp l ∗ ownCtx t s C p pp (some (nodeMaxO l.maxEnd e mh)))

theorem ownCtx_top (t s n p : Loc) (mh : Option GoString) :
    ownCtx (GF := GF) t s .top n p mh = iprop(⌜p = s⌝ ∗ t.[intervalTree, go!"root"] ↦ n) := by
  rw [ownCtx]

theorem ownCtx_inL (t s : Loc) (c : RbColor) (C : RbCtx Entry) (e : Entry) (r : RbT Entry)
    (n p : Loc) (mh : Option GoString) :
    ownCtx (GF := GF) t s (.inL c C e r) n p mh = iprop(∃ pp rp : Loc, ⌜p ≠ s ∧ p ≠ null⌝ ∗
      p.[intervalNode, go!"iv"] ↦
        ({ Ivl' := affIvl e.1.1 e.1.2, Val' := e.2 } : IntervalValue) ∗
      p.[intervalNode, go!"max"] ↦ maxW (nodeMaxO mh e r.maxEnd) ∗
      p.[intervalNode, go!"left"] ↦ n ∗
      p.[intervalNode, go!"right"] ↦ rp ∗
      p.[intervalNode, go!"parent"] ↦ pp ∗
      p.[intervalNode, go!"c"] ↦ colorW c ∗
      ownNode s 1 p rp r ∗ ownCtx t s C p pp (some (nodeMaxO mh e r.maxEnd))) := by
  rw [ownCtx]

theorem ownCtx_inR (t s : Loc) (c : RbColor) (l : RbT Entry) (e : Entry) (C : RbCtx Entry)
    (n p : Loc) (mh : Option GoString) :
    ownCtx (GF := GF) t s (.inR c l e C) n p mh = iprop(∃ pp lp : Loc, ⌜p ≠ s ∧ p ≠ null⌝ ∗
      p.[intervalNode, go!"iv"] ↦
        ({ Ivl' := affIvl e.1.1 e.1.2, Val' := e.2 } : IntervalValue) ∗
      p.[intervalNode, go!"max"] ↦ maxW (nodeMaxO l.maxEnd e mh) ∗
      p.[intervalNode, go!"left"] ↦ lp ∗
      p.[intervalNode, go!"right"] ↦ n ∗
      p.[intervalNode, go!"parent"] ↦ pp ∗
      p.[intervalNode, go!"c"] ↦ colorW c ∗
      ownNode s 1 p lp l ∗ ownCtx t s C p pp (some (nodeMaxO l.maxEnd e mh))) := by
  rw [ownCtx]

/-- The hole's parent is the sentinel exactly at the top. -/
theorem ownCtx_parent (t s : Loc) (C : RbCtx Entry) (n p : Loc) (mh : Option GoString) :
    ownCtx (GF := GF) t s C n p mh ⊢ ⌜C = .top ↔ p = s⌝ := by
  cases C with
  | top => rw [ownCtx_top]; iintro ⟨%h, -⟩; ipureintro <;> simp [h]
  | inL c C e r =>
    rw [ownCtx_inL]; iintro ⟨%pp, %rp, %h, -⟩; ipureintro; simp [h.1]
  | inR c l e C =>
    rw [ownCtx_inR]; iintro ⟨%pp, %lp, %h, -⟩; ipureintro; simp [h.1]

/-- At the top, the hole's max does not matter. -/
theorem ownCtx_top_any (t s n p : Loc) (mh mh' : Option GoString) :
    ownCtx (GF := GF) t s .top n p mh ⊢ ownCtx t s .top n p mh' := by
  rw [ownCtx_top, ownCtx_top]

/-- **One level up**: the hole's subtree with its parent's frame is the parent's subtree. -/
theorem ownCtx_up_inL (t s : Loc) (c : RbColor) (C : RbCtx Entry) (e : Entry) (r : RbT Entry)
    (n p : Loc) (T : RbT Entry) :
    ownCtx (GF := GF) t s (.inL c C e r) n p T.maxEnd ∗ ownNode s 1 p n T ⊢
      ∃ pp, ownCtx t s C p pp (some (nodeMax T e r)) ∗ ownNode s 1 pp p (.node c T e r) := by
  rw [ownCtx_inL]
  iintro ⟨⟨%pp, %rp, %Hp, Hiv, Hmx, Hl, Hr, Hpp, Hc, Hnr, HC⟩, Hn⟩
  iexists pp
  rw [nodeMax_eq]
  iframe HC
  iapply ownNode_node_close
  iexists n, rp
  simp only [nodeMax_eq]
  iframe
  ipureintro; exact Hp

theorem ownCtx_up_inR (t s : Loc) (c : RbColor) (l : RbT Entry) (e : Entry) (C : RbCtx Entry)
    (n p : Loc) (T : RbT Entry) :
    ownCtx (GF := GF) t s (.inR c l e C) n p T.maxEnd ∗ ownNode s 1 p n T ⊢
      ∃ pp, ownCtx t s C p pp (some (nodeMax l e T)) ∗ ownNode s 1 pp p (.node c l e T) := by
  rw [ownCtx_inR]
  iintro ⟨⟨%pp, %lp, %Hp, Hiv, Hmx, Hl, Hr, Hpp, Hc, Hnl, HC⟩, Hn⟩
  iexists pp
  rw [nodeMax_eq]
  iframe HC
  iapply ownNode_node_close
  iexists lp, n
  simp only [nodeMax_eq]
  iframe
  ipureintro; exact Hp

/-- **One level down**, to the left child. -/
theorem ownCtx_down_left (t s : Loc) (C : RbCtx Entry) (n p : Loc) (c : RbColor)
    (l : RbT Entry) (e : Entry) (r : RbT Entry) :
    ownCtx (GF := GF) t s C n p (some (nodeMax l e r)) ∗ ownNode s 1 p n (.node c l e r) ⊢
      ∃ lp, ownCtx t s (.inL c C e r) lp n l.maxEnd ∗ ownNode s 1 n lp l := by
  iintro ⟨HC, Hn⟩
  icases ownNode_node_open _ _ _ _ c l e r $$ Hn with
    ⟨%lp, %rp, %Hn, Hiv, Hmx, Hl, Hr, Hp, Hc, Hnl, Hnr⟩
  iexists lp
  iframe Hnl
  rw [ownCtx_inL]
  iexists p, rp
  simp only [nodeMax_eq]
  iframe
  ipureintro; exact Hn

/-- **One level down**, to the right child. -/
theorem ownCtx_down_right (t s : Loc) (C : RbCtx Entry) (n p : Loc) (c : RbColor)
    (l : RbT Entry) (e : Entry) (r : RbT Entry) :
    ownCtx (GF := GF) t s C n p (some (nodeMax l e r)) ∗ ownNode s 1 p n (.node c l e r) ⊢
      ∃ rp, ownCtx t s (.inR c l e C) rp n r.maxEnd ∗ ownNode s 1 n rp r := by
  iintro ⟨HC, Hn⟩
  icases ownNode_node_open _ _ _ _ c l e r $$ Hn with
    ⟨%lp, %rp, %Hn, Hiv, Hmx, Hl, Hr, Hp, Hc, Hnl, Hnr⟩
  iexists rp
  iframe Hnr
  rw [ownCtx_inR]
  iexists p, lp
  simp only [nodeMax_eq]
  iframe
  ipureintro; exact Hn

/-- One level down to the left child, from the node's fields (a descent that read them). -/
theorem ownCtx_push_inL (t s : Loc) (C : RbCtx Entry) (x y : Loc) (c : RbColor)
    (l : RbT Entry) (e : Entry) (r : RbT Entry) (lp rp : Loc) (hx : x ≠ s ∧ x ≠ null) :
    ownCtx (GF := GF) t s C x y (some (nodeMax l e r)) ∗
      x.[intervalNode, go!"iv"] ↦
        ({ Ivl' := affIvl e.1.1 e.1.2, Val' := e.2 } : IntervalValue) ∗
      x.[intervalNode, go!"max"] ↦ maxW (nodeMax l e r) ∗
      x.[intervalNode, go!"left"] ↦ lp ∗ x.[intervalNode, go!"right"] ↦ rp ∗
      x.[intervalNode, go!"parent"] ↦ y ∗ x.[intervalNode, go!"c"] ↦ colorW c ∗
      ownNode s 1 x rp r ⊢ ownCtx t s (.inL c C e r) lp x l.maxEnd := by
  iintro ⟨HC, Hiv, Hmx, Hl, Hr, Hp, Hc, Hnr⟩
  rw [ownCtx_inL]
  iexists y, rp
  simp only [nodeMax_eq]
  iframe
  ipureintro; exact hx

/-- One level down to the right child, from the node's fields. -/
theorem ownCtx_push_inR (t s : Loc) (C : RbCtx Entry) (x y : Loc) (c : RbColor)
    (l : RbT Entry) (e : Entry) (r : RbT Entry) (lp rp : Loc) (hx : x ≠ s ∧ x ≠ null) :
    ownCtx (GF := GF) t s C x y (some (nodeMax l e r)) ∗
      x.[intervalNode, go!"iv"] ↦
        ({ Ivl' := affIvl e.1.1 e.1.2, Val' := e.2 } : IntervalValue) ∗
      x.[intervalNode, go!"max"] ↦ maxW (nodeMax l e r) ∗
      x.[intervalNode, go!"left"] ↦ lp ∗ x.[intervalNode, go!"right"] ↦ rp ∗
      x.[intervalNode, go!"parent"] ↦ y ∗ x.[intervalNode, go!"c"] ↦ colorW c ∗
      ownNode s 1 x lp l ⊢ ownCtx t s (.inR c l e C) rp x r.maxEnd := by
  iintro ⟨HC, Hiv, Hmx, Hl, Hr, Hp, Hc, Hnl⟩
  rw [ownCtx_inR]
  iexists y, lp
  simp only [nodeMax_eq]
  iframe
  ipureintro; exact hx

/-- **The whole tree**: the context with its hole's subtree. -/
theorem ownCtx_plug (t s : Loc) : ∀ (C : RbCtx Entry) (n p : Loc) (T : RbT Entry),
    ownCtx (GF := GF) t s C n p T.maxEnd ∗ ownNode s 1 p n T ⊢
      ∃ r, t.[intervalTree, go!"root"] ↦ r ∗ ownNode s 1 s r (C.plug T)
  | .top, n, p, T => by
    rw [ownCtx_top]
    iintro ⟨⟨%Hp, Hr⟩, Hn⟩
    subst Hp
    iexists n
    rw [RbCtx.plug_top]
    iframe
  | .inL c C e r, n, p, T => by
    iintro H
    icases ownCtx_up_inL t s c C e r n p T $$ H with ⟨%pp, HC, Hn⟩
    rw [RbCtx.plug_inL]
    iapply ownCtx_plug t s C p pp (.node c T e r)
    rw [maxEnd_node]
    iframe
  | .inR c l e C, n, p, T => by
    iintro H
    icases ownCtx_up_inR t s c l e C n p T $$ H with ⟨%pp, HC, Hn⟩
    rw [RbCtx.plug_inR]
    iapply ownCtx_plug t s C p pp (.node c l e T)
    rw [maxEnd_node]
    iframe

/-- **The whole tree as a context**: the root's subtree in the top context. -/
theorem ownCtx_root (t s r : Loc) (T : RbT Entry) :
    t.[intervalTree, go!"root"] ↦ r ∗ ownNode (GF := GF) s 1 s r T ⊢
      ownCtx t s .top r s T.maxEnd ∗ ownNode s 1 s r T := by
  rw [ownCtx_top]
  iintro ⟨Hr, Hn⟩
  iframe
  ipureintro; rfl

/-! ## A child's `max`, a node's colour -/

/-- What `updateMax` reads of a child `n`: nothing at the sentinel (no max), else its `max`. -/
def childMax (s n : Loc) : Option GoString → IProp GF
  | none => iprop(⌜n = s⌝)
  | some m => iprop(⌜n ≠ s⌝ ∗ n.[intervalNode, go!"max"] ↦ maxW m)

theorem childMax_none (s n : Loc) : childMax (GF := GF) s n none = iprop(⌜n = s⌝) := rfl
theorem childMax_some (s n : Loc) (m : GoString) :
    childMax (GF := GF) s n (some m) =
      iprop(⌜n ≠ s⌝ ∗ n.[intervalNode, go!"max"] ↦ maxW m) := rfl

/-- A subtree's root `max` field, lent out. -/
theorem ownNode_childMax (s p n : Loc) (T : RbT Entry) :
    ownNode (GF := GF) s 1 p n T ⊢
      childMax s n T.maxEnd ∗ (childMax s n T.maxEnd -∗ ownNode s 1 p n T) := by
  cases T with
  | leaf =>
    rw [ownNode_leaf, maxEnd_leaf, childMax_none]
    iintro %h
    isplitl []
    · ipureintro; exact h
    iintro -; ipureintro; exact h
  | node c l e r =>
    iintro H
    icases ownNode_node_open _ _ _ _ c l e r $$ H with
      ⟨%lp, %rp, %Hn, Hiv, Hmx, Hl, Hr, Hp, Hc, Hnl, Hnr⟩
    rw [maxEnd_node, childMax_some]
    iframe Hmx
    isplitl []
    · ipureintro; exact Hn.1
    iintro ⟨-, Hmx⟩
    iapply ownNode_node_close
    iexists lp, rp
    iframe
    ipureintro; exact Hn

/-- What `x.color(sentinel)` reads: nothing at the sentinel (black), else the `c` field. -/
def colorAt (s x : Loc) (c : RbColor) (dq : DFrac) : IProp GF :=
  iprop(⌜x = s ∧ c = .black⌝ ∨ (⌜x ≠ s⌝ ∗ x.[intervalNode, go!"c"] ↦{dq} colorW c))

/-- The hole's parent's colour (the sentinel's, black, at the top), lent out. -/
theorem ownCtx_colorAt (t s : Loc) (C : RbCtx Entry) (n p : Loc) (mh : Option GoString) :
    ownCtx (GF := GF) t s C n p mh ⊢
      colorAt s p C.color (DFrac.own 1) ∗
        (colorAt s p C.color (DFrac.own 1) -∗ ownCtx t s C n p mh) := by
  cases C with
  | top =>
    rw [ownCtx_top]
    iintro ⟨%h, Hr⟩
    isplitl []
    · unfold colorAt; ileft; ipureintro; exact ⟨h, rfl⟩
    iintro -
    iframe; ipureintro; exact h
  | inL c C e r =>
    rw [ownCtx_inL]
    iintro ⟨%pp, %rp, %Hp, Hiv, Hmx, Hl, Hr, Hpp, Hc, Hnr, HC⟩
    isplitl [Hc]
    · unfold colorAt; simp only [RbCtx.color]; iright; iframe; ipureintro; exact Hp.1
    iintro Hc
    unfold colorAt
    simp only [RbCtx.color]
    icases Hc with (⟨%h, -⟩ | ⟨-, Hc⟩)
    · exact absurd h Hp.1
    iexists pp, rp
    iframe; ipureintro; exact Hp
  | inR c l e C =>
    rw [ownCtx_inR]
    iintro ⟨%pp, %lp, %Hp, Hiv, Hmx, Hl, Hr, Hpp, Hc, Hnl, HC⟩
    isplitl [Hc]
    · unfold colorAt; simp only [RbCtx.color]; iright; iframe; ipureintro; exact Hp.1
    iintro Hc
    unfold colorAt
    simp only [RbCtx.color]
    icases Hc with (⟨%h, -⟩ | ⟨-, Hc⟩)
    · exact absurd h Hp.1
    iexists pp, lp
    iframe; ipureintro; exact Hp

/-- A subtree's root's colour (the sentinel's, black, for the leaf), lent out. -/
theorem ownNode_colorAt (s p n : Loc) (T : RbT Entry) :
    ownNode (GF := GF) s 1 p n T ⊢
      colorAt s n T.color (DFrac.own 1) ∗
        (colorAt s n T.color (DFrac.own 1) -∗ ownNode s 1 p n T) := by
  cases T with
  | leaf =>
    rw [ownNode_leaf]
    iintro %h
    isplitl []
    · unfold colorAt; ileft; ipureintro; exact ⟨h, rfl⟩
    iintro -; ipureintro; exact h
  | node c l e r =>
    iintro H
    icases ownNode_node_open _ _ _ _ c l e r $$ H with
      ⟨%lp, %rp, %Hn, Hiv, Hmx, Hl, Hr, Hp, Hc, Hnl, Hnr⟩
    isplitl [Hc]
    · unfold colorAt; simp only [RbT.color_node]; iright; iframe; ipureintro; exact Hn.1
    iintro Hc
    unfold colorAt
    simp only [RbT.color_node]
    icases Hc with (⟨%h, -⟩ | ⟨-, Hc⟩)
    · exact absurd h Hn.1
    iapply ownNode_node_close
    iexists lp, rp
    iframe; ipureintro; exact Hn

/-- A subtree's root's colour, to be written black (`insertFixup`'s last line on the root). -/
theorem ownNode_blacken (s p n : Loc) (c : RbColor) (l : RbT Entry) (e : Entry)
    (r : RbT Entry) :
    ownNode (GF := GF) s 1 p n (.node c l e r) ⊢
      n.[intervalNode, go!"c"] ↦ colorW c ∗
        (n.[intervalNode, go!"c"] ↦ colorW .black -∗ ownNode s 1 p n (.node .black l e r)) := by
  iintro H
  icases ownNode_node_open _ _ _ _ c l e r $$ H with
    ⟨%lp, %rp, %Hn, Hiv, Hmx, Hl, Hr, Hp, Hc, Hnl, Hnr⟩
  iframe Hc
  iintro Hc
  iapply ownNode_node_close
  iexists lp, rp
  iframe; ipureintro; exact Hn

/-! ## Distinct nodes -/

omit package_sem in
/-- Two full points-tos of a pointer field are not of the same location. -/
theorem locField_excl (a : Loc) (v w : Loc) :
    a ↦ v ∗ a ↦ w ⊢ (False : IProp GF) := by
  rw [typedPointsto_unseal]; unfold typedPointstoWrap
  iintro ⟨⟨H1, _⟩, ⟨H2, _⟩⟩
  simp only [typedPointstoDef_heap]
  icombine H1 H2 gives % ⟨Hbad, _⟩
  exfalso
  have : (1 + 1 : Rat) ≤ 1 := Hbad
  grind

/-- A subtree's root is not a node whose `parent` field is owned elsewhere. -/
theorem ownNode_ne (s p n x px : Loc) (T : RbT Entry) (hx : x ≠ s) :
    ownNode (GF := GF) s 1 p n T ⊢ x.[intervalNode, go!"parent"] ↦ px -∗ ⌜n ≠ x⌝ := by
  cases T with
  | leaf =>
    rw [ownNode_leaf]
    iintro %h -
    ipureintro; rintro rfl; exact hx h
  | node c l e r =>
    iintro H Hx
    icases ownNode_node_open _ _ _ _ c l e r $$ H with
      ⟨%lp, %rp, %Hn, -, -, -, -, Hp, -⟩
    by_cases h : n = x
    · subst h
      iexfalso
      iapply locField_excl
      iframe
    · ipureintro; exact h

/-- A node other than the sentinel: its `parent` field is not the sentinel's. -/
theorem ownSentinel_ne (s z w : Loc) :
    ownSentinel (GF := GF) s 1 ⊢ z.[intervalNode, go!"parent"] ↦ w -∗ ⌜z ≠ s⌝ := by
  unfold ownSentinel
  iintro ⟨%v, H⟩ Hz
  by_cases h : z = s
  · subst h
    iStructNamed H
    iexfalso
    iapply locField_excl
    iframe
  · ipureintro; exact h

omit package_sem in
/-- The tree struct from its fields. -/
theorem ivt_combine (t r s : Loc) (c : w64) (ht : t ≠ null) :
    t.[intervalTree, go!"root"] ↦ r ∗ t.[intervalTree, go!"count"] ↦ c ∗
      t.[intervalTree, go!"sentinel"] ↦ s ⊢
      (t ↦ ({ root' := r, count' := c, sentinel' := s } : intervalTree) : IProp GF) := by
  iintro ⟨Hr, Hc, Hs⟩
  iapply typedPointsto_combine _ _ _ ht
  simp only [TypedPointsto.typedPointstoDef]
  iframe

end ctx

end adt
end EtcdGrove
end Perennial
