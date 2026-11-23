/-
`(*rate.Limiter).WaitN(ctx, n)` (x/time/rate v0.16.0, `rate.go:237-249`: `wait` with the real timer
generator; rate-wait, 2026-11-23). Lean-first.
-/
module

public import Spec.golang_org.x.time.rate.Limiter__Wait

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI golang_org.x.time

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : golang_org.x.time.rate.Assumptions]

/-- **`rl.WaitN(ctx, n)`** of a rate limiter, a context and any count: waits (or not) and returns
some error, as `Wait` (`rate.Limiter.Wait.spec`). -/
abbrev rate.Limiter.WaitN.spec : Prop :=
  ∀ (rl : Loc) (c : GoInterfaceOk) (cd : _root_.Perennial.context.ContextDesc (IProp GF)) (n : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.golang_org.x.time.rate ∗ rate.limiterOk rl ∗
      _root_.Perennial.context.isContext c cd }}
    (App (App (Val (rl @!! go.GoType.PointerType rate.Limiter.ty @!! go!"WaitN"))
      (Val #(GoInterface.ok c))) (Val #n))
  {{ (err : GoInterface), RET #err; True }}

end spec

end EtcdGrove
end Perennial
