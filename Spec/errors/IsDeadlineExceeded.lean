/-
`errors.Is(err, context.DeadlineExceeded)`: `errors.Is` at the one target `errors.wp_Is` does
not take, `context.DeadlineExceeded`, which holds `deadlineExceededError{}` (an empty struct, not
a pointer). Lean-first (no Rocq counterpart); `togRPCError`'s (2026-10-12, the request path's
unit 1). `parseProposeCtxErr`'s `errors.Is` is `errors.IsCtxErr`: its error is a context's (no
error tree), this one's an applier's (an error tree, no context type).

Go's `Is` finds the target's type comparable by reflection (an empty struct is) and compares the
target with each error of `err`'s tree (`==`): two interfaces of different dynamic types are
unequal, and two `deadlineExceededError`s equal, so no comparison panics; the rest is the tree
walk of `errors.wp_Is` (`err`'s `Is` and `Unwrap` methods, `errors.errorIsTree`). Perennial's
`errors.wp_Is` covers pointer targets only (its model of `reflectlite`'s `Comparable` says
nothing of other types, and its tree walk compares pointers): so this is an axiom
(`Proof/errors/IsDeadlineExceeded.lean`). The target is the value the package variable holds
(`deadlineExceededError{}`, `context.wp_initialize'`; never written after).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.Base

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : _root_.Perennial.errors.Assumptions]

/-- `errors.Is(err, target)` for `target` the value of `context.DeadlineExceeded` and an `err`
in an error tree: `true` only if some error of the tree has `target`'s dynamic type or has an
`Is` method that returned `true` (`M`). (PR etcd#21684's verification, 2026-10-17: the
postcondition was `True`; `togRPCError`'s spec needs `errors.Is(lease.ErrNotPrimary,
context.DeadlineExceeded)` to be `false`. Go's `Is` returns `true` only from its loop's
`isComparable && err == target`, and two interfaces are `==` only at the same dynamic type, or
from `x.Is(target)`, at an error of the tree its `Unwrap` walk reaches. It is stated by type, not
as `ok ii = target`: the model's `==` of two values of the empty struct `deadlineExceededError`
is `true` whatever the values, and without Go's typing an error of the tree may hold another
value of that type; the reviewer of PR etcd#21684 found the first statement false of the model.) -/
abbrev errors.IsDeadlineExceeded.spec : Prop :=
  ∀ (S : GoInterface → Prop) (M : GoInterfaceOk → Prop) (err target : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.errors ∗
      globalAddr _root_.Perennial.context.DeadlineExceeded ↦□ target ∗
      _root_.Perennial.errors.errorIsTree (GF := GF) S M target ∗ ⌜S err⌝ }}
    (App (App (Val (@! _root_.Perennial.errors.Is)) (Val #err)) (Val #target))
  {{ (b : Bool), RET #b;
      ⌜b = true → ∃ ii, S (GoInterface.ok ii) ∧
        ((∃ tii, target = GoInterface.ok tii ∧ ii.ty = tii.ty) ∨ M ii)⌝ }}

end spec

end EtcdGrove
end Perennial
