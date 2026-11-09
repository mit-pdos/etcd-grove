/-
`(*grpc.Server).Serve(lis)` (grpc-go, assumed: `server.go`).

Users: 2e's `Serve` of a member (`embed`'s `serveCtx.serve`, `examples/lib/etcdstart`'s `Serve`).

Why true: `Serve` accepts connections on `lis` and, per request, runs the registered handler on a
goroutine of its own, which draws one of the caller's thread tokens from the pool `start` took
(the physical premise: at most `n` runs at once) and returns it; it returns an error when the
listener fails or the server stops. What each run must meet was fixed when the right to serve was
granted (`start.spec`), so `Serve` itself takes only that right.

Changes: from `specs-ref/Spec/google_golang_org/grpc/Server__Serve.lean` and the old `grpc.serve`
axiom: the handler pool (`S`, `n`, chosen by the caller: `notes/per-type-blockers.md` (a)) is gone;
each run borrows a token from the caller's pool (round 1, 2f's `Http.handlerPool`); the replies' size premise (`grpcRepliesFit`) is `msgsFit`, taken
by `start`.

Margin: none.
-/
module

public import Spec.google_golang_org.grpc.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Grpc

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- `gs.Serve(lis)` with the right to serve: returns an error when it stops. -/
def Server.Serve.spec : Prop :=
  ∀ (gs : Loc) (lis : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.grpc ∗ serveTok gs lis }}
    (App (Val (gs @!! go.GoType.PointerType google_golang_org.grpc.Server.ty @!! go!"Serve")) (Val #lis))
  {{ (err : GoInterface), RET #err; True }}

end spec

end Grpc
end EtcdGrove
end Perennial
