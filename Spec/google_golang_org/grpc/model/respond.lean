/-
`grpc.model.respond(s, r, resp, err)` (per-type stage B, B1a, 2026-11-11; Scope r5 §2.2): a leaf of the trusted `Serve` model
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

/-- **respond** -- the composite: the reply path after a unary handler, in v1.84's unified pipeline:
`wrapUnaryHandler`'s `stream.SendMsg(reply)` (`server.go:1281-1289`; `serverStream.SendMsg`: the
codec's encode, the size check against the send limit, the transport's `write`,
`http2_server.go:1160`), then `processRPC`'s status paths (`server.go:1459-1515`: on error
`status.FromError` (:1461) and `ss.writeStatus(appStatus)` (:1494); on success
`ss.writeStatus(statusOK)` (:1513); `http2Server.writeStatus`, `http2_server.go:1089`). Under `grpcRepliesFit` the
marshalled reply does not exceed `grpcReplyMax`, so the codec's `make` does not panic
(`notes/reply-size.md`). The reply (or the handler's error) is the one the client's `Invoke` returns
(`InvGrpcRun.lean`, "The pair"). -/
abbrev grpc.model.respond.spec : Prop :=
  ∀ (gs : Loc) (r : val) (resp err : GoInterface) (Rep : ProtoMsgT GF) (Φ : Rep.M → IProp GF)
    (Ψe : GoString → IProp GF),
  {{ grpcReplyTo r Rep Φ Ψe ∗ ⌜grpcRepliesFit⌝ ∗ go_etcd_io.etcd.cache.v3.srvErrOk err ∗
      (⌜err = GoInterface.nil⌝ -∗ ∃ (l : Loc) (m' : Rep.M),
        ⌜resp = interface.mkOk (go.GoType.PointerType Rep.ty) #l⌝ ∗ Rep.send l m' ∗ Φ m') ∗
      (⌜err ≠ GoInterface.nil ∧ go_etcd_io.etcd.cache.v3.errDesc err ∈ handlerDescs⌝ -∗
        Ψe (go_etcd_io.etcd.cache.v3.errDesc err)) }}
    (App (App (App (App (Val (@! google_golang_org.grpc.model.respondName)) (Val #gs)) (Val r))
      (Val #resp)) (Val #err))
  {{ RET #(); True }}

end spec

end EtcdGrove
end Perennial
