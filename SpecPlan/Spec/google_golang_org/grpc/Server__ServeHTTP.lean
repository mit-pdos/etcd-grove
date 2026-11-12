/-
`(*grpc.Server).ServeHTTP(w, r)` (grpc-go, assumed: `server.go`, `internal/transport/handler_server.go`).

Users: etcd's TLS client path: embed's `grpcHandlerFunc` hands every request that is a gRPC call to
it, from net/http's server (`embed/serve.go:260,314-324`, 2e).

Why true: for an HTTP/2 `POST` with a gRPC content type it runs the method's handler as `Serve`
would (decoding the request, the interceptors, the registered handler), on net/http's handler
goroutine, and writes the reply or the status as the response; what the client then decodes is
the protocol `grpcOver C P` says for a gRPC call. The run's thread token is net/http's handler
run's (2f's `servePre`).

Changes: new (round 1, completeness F4 and provability F1/F7).

Margin: a request that is not a gRPC call is not specified (grpc answers it with an error status;
etcd never passes one).
-/
module

public import SpecPlan.Spec.google_golang_org.grpc.Api

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

/-- `gs.ServeHTTP(w, r)` of a gRPC call, on a server started for `ServeHTTP`: a run of net/http's
handler contract for the protocol `grpcOver C P`. -/
def Server.ServeHTTP.spec : Prop :=
  ∀ (gs : Loc) (C : AddrContract (GF := GF)) (P : Http.Proto GF) (w : GoInterface) (r : Loc)
    (R : Http.HReq) (τ : GName) (rd : GoInterface),
  isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.grpc ∗ servesHTTP gs C ∗ ⌜grpcReq R⌝ ∗ Http.servePre (grpcOver C P) go!"/" w r R τ rd ⊢
    WP (App (App (Val (gs @!! go.GoType.PointerType google_golang_org.grpc.Server.ty @!! go!"ServeHTTP")) (Val #w)) (Val #r))
      {{ v, Http.serveDone (grpcOver C P) w R τ v }}

end spec

end Grpc
end EtcdGrove
end Perennial
