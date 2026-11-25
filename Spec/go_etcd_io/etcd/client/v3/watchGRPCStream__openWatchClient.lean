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
accepts (the stream's context's, or `rpctypes.Error` of a halting one). Since G2 (2026-10-30), the
stream was opened with metadata `md` an attempt on the connection delivered for the stream's
context (`clientAttemptMd`), and its specification is at `md`'s token (`auth.mdTokenOf`). Since phase
7's switch (SW1, 2026-11-24, R2): the member and the metadata are not fixed when the stream is
returned (a transparent retry may re-pick both): the requests' content is every member's
(`watchUpW`), and the specification holds at every dispatch the client may learn with a response
(`watchMdW`: a member's address and an attempt's metadata), at that dispatch's content. -/
abbrev watchGRPCStream.openWatchClient.spec : Prop :=
  ∀ (V : WEnv GF) (wgs : Loc) (ci : GoInterfaceOk) (cd : context.ContextDesc (IProp GF))
    (om : GrpcMd) (callSl : GoSlice) (vs : List GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.etcdserverpb ∗ levelTok 0 ∗ (wgsF wgs go!"ctx" ↦□ (GoInterface.ok ci) ∗ context.isContext ci cd ∗ metadata.outMD ci om ∗
      wgsF wgs go!"remote" ↦□ wcIface V.wc ∗ wgsF wgs go!"callOpts" ↦□ callSl ∗
      callSl ↦*□ vs ∗ callOptsOk vs ∗ watchSrvFacts V) }}
    (App (Val (wgs @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.watchGRPCStream.ty @!! go!"openWatchClient")) (Val #()))
  {{ (ws err : GoInterface), RET (PairV #ws #err); levelTok 0 ∗ ((⌜err = GoInterface.nil⌝ ∗ ∃ (γs : StreamNames)
          (Dn : GoString → GrpcMd → Nat → v3rpc.WatchRespM → IProp GF)
          (cd' : context.ContextDesc (IProp GF)),
        -- (SW1, R2) at the member and the metadata each response tells
        v3rpc.cliWatchStreamIs ws γs (watchUpW V) (watchMdW V om) Dn cd' ∗
        cliSendTok (Req := v3rpc.pbWatchRequest) γs [] ∗
        cliRecvTok (Rep := v3rpc.pbWatchResponse) γs [] ∗
        □ (∀ a md, watchMdW V om a md -∗
          v3rpc.watchSpec (V.memOf a) (V.memWOf a) (auth.mdTokenOf md) γs (Dn a md))) ∨
      (⌜ws = GoInterface.nil ∧ err ≠ GoInterface.nil⌝ ∗ closeErrOk err)) }}

end spec

end EtcdGrove
end Perennial
