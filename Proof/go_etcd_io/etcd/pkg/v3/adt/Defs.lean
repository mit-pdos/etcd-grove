/-
The Go values of the interval tree's model (`Model.lean`, `Tree.lean`): a string-affine
interval as the Go `Interval`, and the tree's ownership predicate `ownIvt` (the red-black tree's
representation: the nodes over the model `RbT`, the sentinel, the in-order list). Lean-first; see
`notes/decisions.md`, "The watchable store: the plan, the interval tree's contract".
-/
module

public import Proof.go_etcd_io.etcd.pkg.v3.adt.Base
public import Proof.go_etcd_io.etcd.pkg.v3.adt.Tree

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace adt

open Iris Iris.BI go_etcd_io.etcd.pkg.v3.adt

section defs
variable [ext : FfiSyntax] [GoGlobalContext]

/-- The affine interval value `[b, e)` as the Go `Interval` (its `Comparable`s are
`StringAffineComparable`s): what `NewStringAffineInterval(b, e)` returns. -/
def affIvl (b e : GoString) : Interval :=
  { Begin' := interface.mkOk StringAffineComparable.ty #b,
    End' := interface.mkOk StringAffineComparable.ty #e }

@[simp] theorem affIvl_Begin (b e : GoString) :
    (affIvl b e).Begin' = interface.mkOk StringAffineComparable.ty #b := rfl
@[simp] theorem affIvl_End (b e : GoString) :
    (affIvl b e).End' = interface.mkOk StringAffineComparable.ty #e := rfl

end defs

section reprs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.pkg.v3.adt.Assumptions]

/-- A node's colour as its Go value (`black` is `0`, `red` is `1`). -/
def colorW : RbColor → w64
  | .black => W64 0
  | .red => W64 1

/-- A node's `max` field: the subtree's largest end, as a `StringAffineComparable`. -/
def maxW (m : GoString) : GoInterface := interface.mkOk StringAffineComparable.ty #m

/-- The subtree at `n` (child of `p`) holds the model `t`, at the fraction `q`, with the
sentinel `s`: the leaf is the sentinel; a node is a pointer other than the sentinel and `nil`,
with its fields at `q`: `iv` (its entry: `affIvl` of the interval and the value), `max` (the
subtree's largest end, `nodeMax`: exact by construction), `left`/`right` (the children's
subtrees), `parent` (`p`), `c` (its colour). -/
def ownNode (s : Loc) (q : Qp) : Loc → Loc → RbT Entry → IProp GF
  | _, n, .leaf => iprop(⌜n = s⌝)
  | p, n, .node c l e r => iprop(∃ lp rp : Loc, ⌜n ≠ s ∧ n ≠ null⌝ ∗
      n.[intervalNode, go!"iv"] ↦{DFrac.own q}
        ({ Ivl' := affIvl e.1.1 e.1.2, Val' := e.2 } : IntervalValue) ∗
      n.[intervalNode, go!"max"] ↦{DFrac.own q} maxW (nodeMax l e r) ∗
      n.[intervalNode, go!"left"] ↦{DFrac.own q} lp ∗
      n.[intervalNode, go!"right"] ↦{DFrac.own q} rp ∗
      n.[intervalNode, go!"parent"] ↦{DFrac.own q} p ∗
      n.[intervalNode, go!"c"] ↦{DFrac.own q} colorW c ∗
      ownNode s q n lp l ∗ ownNode s q n rp r)

theorem ownNode_leaf (s : Loc) (q : Qp) (p n : Loc) :
    ownNode (GF := GF) s q p n .leaf = iprop(⌜n = s⌝) := by rw [ownNode]

theorem ownNode_node (s : Loc) (q : Qp) (p n : Loc) (c : RbColor) (l : RbT Entry) (e : Entry)
    (r : RbT Entry) :
    ownNode (GF := GF) s q p n (.node c l e r) = iprop(∃ lp rp : Loc, ⌜n ≠ s ∧ n ≠ null⌝ ∗
      n.[intervalNode, go!"iv"] ↦{DFrac.own q}
        ({ Ivl' := affIvl e.1.1 e.1.2, Val' := e.2 } : IntervalValue) ∗
      n.[intervalNode, go!"max"] ↦{DFrac.own q} maxW (nodeMax l e r) ∗
      n.[intervalNode, go!"left"] ↦{DFrac.own q} lp ∗
      n.[intervalNode, go!"right"] ↦{DFrac.own q} rp ∗
      n.[intervalNode, go!"parent"] ↦{DFrac.own q} p ∗
      n.[intervalNode, go!"c"] ↦{DFrac.own q} colorW c ∗
      ownNode s q n lp l ∗ ownNode s q n rp r) := by rw [ownNode]

/-- The sentinel (CLRS's `T.nil`), at the fraction `q`: its fields' values are not specified
(`NewIntervalTree` makes it black with a zero `iv` and `nil` links and `max`; `Delete` and the
fixups write its `parent` and colour, which `color(sentinel)` never reads). -/
def ownSentinel (s : Loc) (q : Qp) : IProp GF :=
  iprop(∃ v : intervalNode, s ↦{DFrac.own q} v)

include sem package_sem in
/-- **The tree at `t` (a `*intervalTree`) holds the entries `L`** (in the tree's order; equal
intervals allowed, in insertion order among equals: `IvSorted`), at the fraction `q` (the reads, `Find`/`Intersects`/`Stab`/`Len`, at any
fraction; `Insert`/`Delete` at `1`: the watchable store reads its groups under its lock's read
side): the tree struct, the sentinel, and the nodes from the root (whose parent is the
sentinel) holding a red-black tree `T` whose in-order list is `L`, with the entry count (below
`2^63`: `Stab` reads `count == 0` as an empty tree, so the count must not wrap). It takes
the semantics as an argument (as the specs on it do). -/
def ownIvt (t : Loc) (L : List Entry) (q : Qp) : IProp GF :=
  iprop(∃ (tv : intervalTree) (T : RbT Entry),
    t ↦{DFrac.own q} tv ∗ ownSentinel tv.sentinel' q ∗
    ownNode tv.sentinel' q tv.sentinel' tv.root' T ∗
    ⌜T.inorder = L ∧ RbOk T ∧ IvSorted L ∧ tv.count' = W64 L.length ∧ L.length < 2 ^ 63⌝)

open Iris.ProofMode in
/-- An `Interval` points-to as its fields. -/
theorem ivl_split (l : Loc) (v : Interval) (dq : DFrac) :
    (l ↦{dq} v : IProp GF) ⊢
      l.[Interval, go!"Begin"] ↦{dq} v.Begin' ∗ l.[Interval, go!"End"] ↦{dq} v.End' ∗
        ⌜l ≠ null⌝ := by
  iintro H
  ihave %Hn := typedPointsto_not_null _ _ _ $$ H
  icases typedPointsto_split _ _ _ $$ H with H
  simp only [TypedPointsto.typedPointstoDef]
  iNamed H
  iframe Begin End
  ipureintro; exact Hn

open Iris.ProofMode in
/-- The fields of an `Interval` as its points-to. -/
theorem ivl_combine (l : Loc) (v : Interval) (dq : DFrac) (h : l ≠ null) :
    l.[Interval, go!"Begin"] ↦{dq} v.Begin' ∗ l.[Interval, go!"End"] ↦{dq} v.End' ⊢
      (l ↦{dq} v : IProp GF) := by
  iintro ⟨Hb, He⟩
  iapply typedPointsto_combine _ _ _ h
  simp only [TypedPointsto.typedPointstoDef]
  iframe Hb He

end reprs

end adt
end EtcdGrove
end Perennial
