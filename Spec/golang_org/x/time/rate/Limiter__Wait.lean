/-
## `(*Limiter).Wait(ctx)`: assumed

**Users.** `streamReader.run` (`rafthttp/stream.go:449`, the reader's context). Snippet: `examples/specreq/pkgleaves/leaves.go`
(`ReqDialRetry`).

**Assumed** (`rate.go:224-280`, `WaitN(ctx, 1)`): under the limiter's mutex, a reservation; an
error if `1 > burst` (with a finite limit), if `ctx` is done, or if the wait would pass `ctx`'s
deadline; else it waits on a timer or `ctx.Done()` and returns `nil` or `ctx.Err()`. It calls `ctx`'s
`Done`, `Err` and `Deadline` (W0's `Context.ctxOk`: a context meeting `context.Context`'s contract).

**Changes.** From `specs-ref`'s `Limiter__Wait.lean` (Perennial's `isContext`): any `ctxOk`.
**Margin.** The error is not described.
-/
module

public import Spec.golang_org.x.time.rate.Api

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Rate

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : golang_org.x.time.rate.Assumptions]

/-- **Waits (or not) and returns some error.** -/
def Limiter.Wait.spec : Prop :=
  ∀ (rl : Loc) (ctx : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.golang_org.x.time.rate ∗ limiterOk rl ∗ Context.ctxOk ctx }}
    (App (Val (rl @!! go.GoType.PointerType golang_org.x.time.rate.Limiter.ty @!! go!"Wait")) (Val #ctx))
  {{ (err : GoInterface), RET #err; True }}

end spec
end Rate
end EtcdGrove
end Perennial
