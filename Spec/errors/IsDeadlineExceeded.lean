/-
`errors.Is(err, context.DeadlineExceeded)`: `errors.Is` at the target `context.DeadlineExceeded`,
which holds `deadlineExceededError{}` (an empty struct, not a pointer). Lean-first (no Rocq
counterpart). Written for `togRPCError` (2026-10-12, the request path's unit 1). `parseProposeCtxErr`'s
`errors.Is` is `errors.IsCtxErr`: its error is a context's (no error tree). This one's is an applier's
or a client's (an error tree, no context type).

Go's `Is` finds the target's type comparable by reflection (an empty struct is). It compares the
target with each error of `err`'s tree (`==`). Two interfaces of different dynamic types are
unequal, and two `deadlineExceededError`s equal, so no comparison panics. The rest is the tree
walk of `errors.wp_Is` (`err`'s `Is` and `Unwrap` methods, `errors.errorIsTree`).

Proved over Perennial's `errors.wp_Is` at comparable targets (perennial#677;
`Proof/errors/IsDeadlineExceeded.lean`). It was a trust-boundary axiom until errors-is-deadline
(2026-11-23): Perennial's `errors.wp_Is` covered pointer targets only.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.Base
public import Proof.errors.CtxErr

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : _root_.Perennial.errors.Assumptions]

/-- `errors.Is(err, target)` for `target` the value of `context.DeadlineExceeded` and an `err`
in an error tree. It returns `true` only if some error of the tree is `target`, or an `Is` method of
the tree said so (`M`), as `errors.Is.spec`'s third conjunct. Go's `errors.is` compares each error of
the walk with `==` and asks its `Is` method (k8s etcd3 7c-2 part 2, G1-a′, 2026-11-06; until then the
post was some boolean).

The errors of the tree whose type is `deadlineExceededError` hold `deadlineExceededError{}`
(`deTyped S`). Go's typing guarantees this, but the model has no typing of interface values, and Go's
`==` with the target needs it (`errors.ComparableErr`). `isPkgInit context` makes `target`
`deadlineExceededError{}` (`context.isInit`'s `"#HDeadlineExceededTy"`). Both were added by
errors-is-deadline (2026-11-23), when the spec was proved (`notes/specs-only/ledger.md`). -/
abbrev errors.IsDeadlineExceeded.spec : Prop :=
  ∀ (S : GoInterface → Prop) (M : GoInterfaceOk → Prop) (err target : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.errors ∗ isPkgInit (PROP := IProp GF) pkg_id.context ∗
      globalAddr _root_.Perennial.context.DeadlineExceeded ↦□ target ∗
      _root_.Perennial.errors.errorIsTree (GF := GF) S M target ∗ ⌜S err⌝ ∗ ⌜deTyped S⌝ }}
    (App (App (Val (@! _root_.Perennial.errors.Is)) (Val #err)) (Val #target))
  {{ (b : Bool), RET #b;
      ⌜b = true → ∃ ii : GoInterfaceOk, S (GoInterface.ok ii) ∧ (GoInterface.ok ii = target ∨ M ii)⌝ }}

end spec

end EtcdGrove
end Perennial
