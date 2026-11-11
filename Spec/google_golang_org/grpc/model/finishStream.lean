/-
`grpc.model.finishStream(s, r, err)` (per-type stage B, B1a, 2026-11-11; Scope r5 §2.2): a leaf of the trusted `Serve` model
(`TrustedCode/google_golang_org/grpcServeModel.lean`), a model-only name with no Go body of its
own. Lean-first (no Rocq counterpart).
-/
module

public import Proof.google_golang_org.grpc.InvGrpcRun

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **finishStream** -- the composite: `processRPC`'s end of a streaming call (`status.FromError` on
the handler's error, then `http2Server.writeStatus`, `http2_server.go:1089`; test T12). -/
abbrev grpc.model.finishStream.spec : Prop :=
  ∀ (gs : Loc) (r : val) (err : GoInterface),
  {{ go_etcd_io.etcd.cache.v3.srvErrOk (GF := GF) err }}
    (App (App (App (Val (@! google_golang_org.grpc.model.finishStreamName)) (Val #gs)) (Val r))
      (Val #err))
  {{ RET #(); True }}

end spec

end EtcdGrove
end Perennial
