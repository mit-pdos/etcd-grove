/-
The Go values of the interval tree's model (`Model.lean`): a string-affine interval as the Go
`Interval`, and the tree's ownership predicate `ownIvt`, opaque until the tree's proof (unit 4
of the watchable store) defines it. Lean-first; see `notes/decisions.md`, "The watchable store:
the plan, the interval tree's contract".
-/
module

public import Proof.go_etcd_io.etcd.pkg.v3.adt.Base
public import Proof.go_etcd_io.etcd.pkg.v3.adt.Model

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

/-- The tree at `t` (a `*intervalTree`) holds the entries `L` (distinct intervals, in the
tree's order), at the fraction `q` (the reads, `Find`/`Intersects`/`Stab`/`Len`, at any
fraction; `Insert`/`Delete` at `1`: the watchable store reads its groups under its lock's read
side). Unit 4 defines it (the red-black tree's representation invariant: the sentinel, the
colours, the `max` augmentation, the in-order list); until then, an opaque constant (a
definition with a hidden body, not an axiom) used only through the contract's triples and the
pending fractionality `adt.ownIvt_split.spec`. Its body names the heap, the semantics and the
package's assumptions so that they are arguments already (`include` does not reach an
`opaque`), as unit 4's definition will need them. -/
opaque ownIvt (t : Loc) (L : List Entry) (q : Qp) : IProp GF :=
  have := hG; have := sem; have := package_sem; have := q; iprop(True)

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
