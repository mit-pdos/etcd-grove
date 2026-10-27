/-
`(*clientv3.watchGRPCStream).openWatchClient()` (`client/v3/watch.go`; (the watch slice's unit W-C). Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.client.v3.InvWatch

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.api.v3 go_etcd_io.etcd.cache.v3 client

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

/-- `w.openWatchClient()` on a stream whose context is a model one (`isContext`), with the
watcher's stub and call options: the client end of a fresh gRPC watch stream (both tokens at
`[]`, the stream's specification `watchSpec`), or a `nil` stream and an error grpc's `status`
accepts (the stream's context's, or `rpctypes.Error` of a halting one). -/
abbrev watchGRPCStream.openWatchClient.spec : Prop :=
  ∀ (V : WEnv GF) (wgs : Loc) (ci : GoInterfaceOk) (cd : context.ContextDesc (IProp GF))
    (callSl : GoSlice) (vs : List GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.etcdserverpb ∗
      wgsF wgs go!"ctx" ↦□ (GoInterface.ok ci) ∗ context.isContext ci cd ∗
      wgsF wgs go!"remote" ↦□ wcIface V.wc ∗ wgsF wgs go!"callOpts" ↦□ callSl ∗
      callSl ↦*□ vs ∗ callOptsOk vs ∗ watchSrvFacts V }}
    (App (Val (wgs @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.watchGRPCStream.ty @!! go!"openWatchClient")) (Val #()))
  {{ (ws err : GoInterface), RET (PairV #ws #err);
      (⌜err = GoInterface.nil⌝ ∗ ∃ (i : Nat) (γs : StreamNames)
          (Dn : Nat → v3rpc.WatchRespM → IProp GF) (cd' : context.ContextDesc (IProp GF)),
        -- (W3b) the stream at some member `i` of the connection's (D32)
        ⌜i < V.nm⌝ ∗ v3rpc.cliWatchStreamIs ws γs (v3rpc.watchUp (V.mem i).2.γ) Dn cd' ∗
        cliSendTok (Req := v3rpc.pbWatchRequest) γs [] ∗
        cliRecvTok (Rep := v3rpc.pbWatchResponse) γs [] ∗ v3rpc.watchSpec (V.mem i).2 γs Dn) ∨
      (⌜ws = GoInterface.nil ∧ err ≠ GoInterface.nil⌝ ∗ statusErrOk err) }}

end spec

end EtcdGrove
end Perennial
