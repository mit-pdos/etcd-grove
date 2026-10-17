/-
`(*clientv3.watchGRPCStream).sendLoop(wc)` (`client/v3/watch.go`, added by etcd-io/etcd#21065;
`notes/pr-verify/etcd-21065.md`). Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.client.v3.InvWatchSend

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.api.v3 go_etcd_io.etcd.cache.v3 client

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

/-- **`w.sendLoop(wc)`**, the stream's only sender (started by `newWatchClient` with the
sender's token): takes requests off the create queue and the best-effort queue (the consumer's
sides) and sends each on the gRPC stream, with what the server's specification asks of it (the
element's `watchUp`), until a queue is closed (`run`, when the stream failed), a send fails, or
the stream is done (`donec`, its context). -/
abbrev watchGRPCStream.sendLoop.spec : Prop :=
  ∀ (V : WEnv GF) (G : WgsPrm GF) (callSl : GoSlice) (Q : SendQ) (wc : GoInterface)
    (γs : StreamNames) (Dn : Nat → v3rpc.WatchRespM → IProp GF) (cd' : context.ContextDesc (IProp GF))
    (L : List v3rpc.WatchReqM) (rc rb : List Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ isWGS V G callSl ∗
      sendQIs V G.wgs Q ∗ v3rpc.cliWatchStreamIs wc γs (v3rpc.watchUp V.R.γ) Dn cd' ∗
      cliSendTok (Req := v3rpc.pbWatchRequest) γs L ∗
      spscConsumer Q.γc rc ∗ spscConsumer Q.γb rb }}
    (App (Val (G.wgs @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.watchGRPCStream.ty @!! go!"sendLoop")) (Val #wc))
  {{ RET #(); True }}

end spec

end EtcdGrove
end Perennial
