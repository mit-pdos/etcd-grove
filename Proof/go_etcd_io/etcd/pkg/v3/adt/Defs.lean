/-
The Go values of the interval tree's model (`Model.lean`, `Tree.lean`), over **a comparator**:
the tree's `Comparable` keys as a key representation `KeyRep` (the auth plan's S2b, 2026-10-23;
`notes/decisions.md`, "S2b of the auth plan"), a string-affine interval as the Go `Interval`
(`affIvl`), and the tree's ownership predicate (the red-black tree's representation: the nodes
over the model `RbT`, the sentinel, the in-order list), generic in the key representation
(`ownIvtK`) and instantiated for string-affine keys (`ownIvt`, `strKey`; the bytes-affine
instance is `BytesIvl.lean`'s). Lean-first; see `notes/decisions.md`, "The watchable store: the
plan, the interval tree's contract".

**The key representation.** The model's keys are Go strings (`GoString`, the key's contents)
under the affine order `affCmp`, for every comparator: what differs between comparators is how a
key is held by a Go value and what a comparison needs. `KeyRep` has the `Comparable`'s dynamic
type (`ty`), and `keyAt dq v k`, the resource "the Go value `v` holds the key `k`" at `dq`:
nothing but `v = #k` for a string (`strKey`), a byte slice's contents for a slice
(`BytesIvl.lean`'s `bytesKey`). A tree's nodes hold their keys read-only (`keyAt .discard`:
persistent, so a key read from a node, as `updateMax`'s `max` and `Contains`' running maximum,
can be copied), and two values of one key agree on it (`keyAt_agree`). The comparison's contract
is `KeyRep.CompareOk`: `v.Compare(v')` returns the affine order of the keys the values hold,
keeping them.
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

/-! ## The key representation -/

/-- **A comparator's key representation**: the `Comparable`'s dynamic type, and how a Go value
holds a key (the model's `GoString`) at a fraction. The nodes' keys are held read-only
(`.discard`), hence persistent; two values of one key agree on it. -/
structure KeyRep where
  /-- The `Comparable`'s dynamic type (`StringAffineComparable.ty`, `BytesAffineComparable.ty`). -/
  ty : go.GoType
  /-- The Go value `v` holds the key `k`, at `dq`. -/
  keyAt : DFrac → val → GoString → IProp GF
  keyAt_persistent : ∀ v k, Persistent (keyAt .discard v k)
  keyAt_agree : ∀ (d d' : DFrac) (v : val) (k k' : GoString), keyAt d v k ∗ keyAt d' v k' ⊢ ⌜k = k'⌝

instance KeyRep.keyAt_persistent_inst (K : KeyRep (GF := GF)) (v : val) (k : GoString) :
    Persistent (K.keyAt .discard v k) := K.keyAt_persistent v k

/-- The interval value `[vb, ve)` of two key values, as the Go `Interval`. -/
def KeyRep.ivl (K : KeyRep (GF := GF)) (vb ve : val) : Interval :=
  { Begin' := interface.mkOk K.ty vb, End' := interface.mkOk K.ty ve }

@[simp] theorem KeyRep.ivl_Begin (K : KeyRep (GF := GF)) (vb ve : val) :
    (K.ivl vb ve).Begin' = interface.mkOk K.ty vb := rfl
@[simp] theorem KeyRep.ivl_End (K : KeyRep (GF := GF)) (vb ve : val) :
    (K.ivl vb ve).End' = interface.mkOk K.ty ve := rfl

theorem KeyRep.ivl_inj (K : KeyRep (GF := GF)) {vb ve vb' ve' : val}
    (h : K.ivl vb ve = K.ivl vb' ve') : vb = vb' ∧ ve = ve' := by
  unfold KeyRep.ivl at h
  simp only [Interval.mk.injEq, GoInterface.ok.injEq, GoInterfaceOk.mk.injEq, true_and] at h
  exact h

/-- **The comparison's contract**: `v.Compare(v')`, for two values holding keys, returns the
affine order of the keys (`affCmp`: `""` the top), keeping the values' resources. -/
def KeyRep.CompareOk (K : KeyRep (GF := GF)) : Prop :=
  ∀ (d d' : DFrac) (v v' : val) (k k' : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.adt ∗
      K.keyAt d v k ∗ K.keyAt d' v' k' }}
    (App (Val #(methods K.ty go!"Compare" v)) (Val #(interface.mkOk K.ty v')))
  {{ RET #(W64 (affCmp k k')); K.keyAt d v k ∗ K.keyAt d' v' k' }}

/-- **A node's `iv` field** (at the location `l`) holds the entry `e`, at `dq`: the interval of
two values holding the entry's keys (read-only), and the value. -/
def KeyRep.ivAt (K : KeyRep (GF := GF)) (l : Loc) (dq : DFrac) (e : Entry) : IProp GF :=
  iprop(∃ vb ve : val, l ↦{dq} ({ Ivl' := K.ivl vb ve, Val' := e.2 } : IntervalValue) ∗
    K.keyAt .discard vb e.1.1 ∗ K.keyAt .discard ve e.1.2)

/-- **A node's `max` field** (at `l`) holds the key `m`, at `dq`: a `Comparable` of a value
holding it (read-only). -/
def KeyRep.maxAt (K : KeyRep (GF := GF)) (l : Loc) (dq : DFrac) (m : GoString) : IProp GF :=
  iprop(∃ vm : val, l ↦{dq} interface.mkOk K.ty vm ∗ K.keyAt .discard vm m)

/-! ## The string-affine keys -/

omit package_sem in
include sem in
/-- Two string values of one key agree on it. -/
theorem str_keyAt_agree (v : val) (k k' : GoString) :
    (iprop(⌜v = #k⌝) : IProp GF) ∗ iprop(⌜v = #k'⌝) ⊢ ⌜k = k'⌝ := by
  iintro ⟨%h1, %h2⟩
  ipureintro
  exact go.intoVal_inj (h1.symm.trans h2)

omit package_sem in
include sem in
/-- **String-affine keys**: a `StringAffineComparable`, the string itself (`v = #k`: no
resource). -/
def strKey : KeyRep (GF := GF) where
  ty := StringAffineComparable.ty
  keyAt := fun _ v k => iprop(⌜v = #k⌝)
  keyAt_persistent := fun _ _ => inferInstance
  keyAt_agree := fun _ _ v k k' => str_keyAt_agree v k k'

omit package_sem in
include sem in
@[simp] theorem strKey_ty : (strKey (GF := GF)).ty = StringAffineComparable.ty := rfl
omit package_sem in
include sem in
theorem strKey_keyAt (d : DFrac) (v : val) (k : GoString) :
    (strKey (GF := GF)).keyAt d v k = iprop(⌜v = #k⌝) := rfl

omit package_sem in
include sem in
theorem affIvl_eq (b e : GoString) : affIvl b e = (strKey (GF := GF)).ivl #b #e := rfl

/-! ## The nodes -/

/-- A node's colour as its Go value (`black` is `0`, `red` is `1`). -/
def colorW : RbColor → w64
  | .black => W64 0
  | .red => W64 1

/-- The subtree at `n` (child of `p`) holds the model `t`, at `dq`, with the sentinel `s`, over
the keys `K`: the leaf is the sentinel; a node is a pointer other than the sentinel and `nil`,
with its fields at `dq`: `iv` (its entry, `K.ivAt`), `max` (the subtree's largest end,
`nodeMax`, exact by construction: `K.maxAt`), `left`/`right` (the children's subtrees),
`parent` (`p`), `c` (its colour). -/
def ownNode (K : KeyRep (GF := GF)) (s : Loc) (dq : DFrac) : Loc → Loc → RbT Entry → IProp GF
  | _, n, .leaf => iprop(⌜n = s⌝)
  | p, n, .node c l e r => iprop(∃ lp rp : Loc, ⌜n ≠ s ∧ n ≠ null⌝ ∗
      K.ivAt n.[intervalNode, go!"iv"] dq e ∗
      K.maxAt n.[intervalNode, go!"max"] dq (nodeMax l e r) ∗
      n.[intervalNode, go!"left"] ↦{dq} lp ∗
      n.[intervalNode, go!"right"] ↦{dq} rp ∗
      n.[intervalNode, go!"parent"] ↦{dq} p ∗
      n.[intervalNode, go!"c"] ↦{dq} colorW c ∗
      ownNode K s dq n lp l ∗ ownNode K s dq n rp r)

theorem ownNode_leaf (K : KeyRep (GF := GF)) (s : Loc) (dq : DFrac) (p n : Loc) :
    ownNode K s dq p n .leaf = iprop(⌜n = s⌝) := by rw [ownNode]

theorem ownNode_node (K : KeyRep (GF := GF)) (s : Loc) (dq : DFrac) (p n : Loc) (c : RbColor)
    (l : RbT Entry) (e : Entry) (r : RbT Entry) :
    ownNode K s dq p n (.node c l e r) = iprop(∃ lp rp : Loc, ⌜n ≠ s ∧ n ≠ null⌝ ∗
      K.ivAt n.[intervalNode, go!"iv"] dq e ∗
      K.maxAt n.[intervalNode, go!"max"] dq (nodeMax l e r) ∗
      n.[intervalNode, go!"left"] ↦{dq} lp ∗
      n.[intervalNode, go!"right"] ↦{dq} rp ∗
      n.[intervalNode, go!"parent"] ↦{dq} p ∗
      n.[intervalNode, go!"c"] ↦{dq} colorW c ∗
      ownNode K s dq n lp l ∗ ownNode K s dq n rp r) := by rw [ownNode]

/-- The sentinel (CLRS's `T.nil`), at `dq`: its fields' values are not specified
(`NewIntervalTree` makes it black with a zero `iv` and `nil` links and `max`; `Delete` and the
fixups write its `parent` and colour, which `color(sentinel)` never reads). -/
def ownSentinel (s : Loc) (dq : DFrac) : IProp GF :=
  iprop(∃ v : intervalNode, s ↦{dq} v)

include sem package_sem in
/-- **The tree at `t` (a `*intervalTree`) holds the entries `L` over the keys `K`** (in the
tree's order; equal intervals allowed, in insertion order among equals: `IvSorted`), at `dq`
(the reads, `Find`/`Intersects`/`Stab`/`Len`, at any fraction, or read-only; `Insert`/`Delete`
at `1`): the tree struct, the sentinel, and the nodes from the root (whose parent is the
sentinel) holding a red-black tree `T` whose in-order list is `L`, with the entry count (below
`2^63`: `Stab` reads `count == 0` as an empty tree, so the count must not wrap). -/
def ownIvtK (K : KeyRep (GF := GF)) (t : Loc) (L : List Entry) (dq : DFrac) : IProp GF :=
  iprop(∃ (tv : intervalTree) (T : RbT Entry),
    t ↦{dq} tv ∗ ownSentinel tv.sentinel' dq ∗
    ownNode K tv.sentinel' dq tv.sentinel' tv.root' T ∗
    ⌜T.inorder = L ∧ RbOk T ∧ IvSorted L ∧ tv.count' = W64 L.length ∧ L.length < 2 ^ 63⌝)

include sem package_sem in
/-- **The tree at `t` holds the entries `L` over string-affine keys**, at the fraction `q`
(the watchable store reads its groups under its lock's read side): `ownIvtK` for `strKey`. -/
def ownIvt (t : Loc) (L : List Entry) (q : Qp) : IProp GF :=
  ownIvtK strKey t L (DFrac.own q)

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
