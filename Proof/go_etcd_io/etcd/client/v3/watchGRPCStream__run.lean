/-
Proof of `Spec/go_etcd_io/etcd/client/v3/watchGRPCStream__run.lean` (the watch slice's unit W-C).
Lean-first (no Rocq counterpart).
-/
module

public import Proof.ReceiptTactics
public import Spec.go_etcd_io.etcd.client.v3.watchGRPCStream__run
public import Proof.go_etcd_io.etcd.client.v3.WatchRun
public import Proof.go_etcd_io.etcd.client.v3.WatchRecon
public import Spec.go_etcd_io.etcd.client.v3.watchGRPCStream__newWatchClient
public import Spec.go_etcd_io.etcd.client.v3.watchGRPCStream__nextResume
public import Spec.go_etcd_io.etcd.client.v3.watchGRPCStream__dispatchEvent
public import Spec.go_etcd_io.etcd.client.v3.watchGRPCStream__addSubstream
public import Spec.go_etcd_io.etcd.client.v3.watchGRPCStream__closeSubstream
public import Spec.go_etcd_io.etcd.client.v3.watchGRPCStream__joinSubstreams
public import Spec.go_etcd_io.etcd.client.v3.watchGRPCStream__serveSubstream
public import Spec.go_etcd_io.etcd.client.v3.watchGRPCStream__newWatcherStreamBufLogger
public import Spec.go_etcd_io.etcd.client.v3.watchRequest__toPB
public import Spec.go_etcd_io.etcd.client.v3.progressRequest__toPB
public import Proof.go_etcd_io.etcd.client.v3.MapSplit
public import Spec.go_etcd_io.etcd.client.v3.watcher__closeStream
public import Spec.go_etcd_io.etcd.client.v3.isHaltErr
public import Spec.go_etcd_io.etcd.client.v3.ContextError
public import Spec.errors.IsStatusErr
public import Spec.go_etcd_io.etcd.client.v3.watchGRPCStream__backoffIfUnavailable
public import Spec.go_uber_org.zap.Logger__Debug
public import Spec.go_uber_org.zap.Error
public import Spec.go_uber_org.zap.Int64
public import Perennial.Proof.time
public import Proof.go_etcd_io.etcd.client.v3.WatchClientModel
public import Proof.go_etcd_io.etcd.client.v3.WatchContent
public import Proof.go_etcd_io.etcd.client.v3.WatchCompl
public import Proof.go_etcd_io.etcd.client.v3.WatchApiLemmas
public import Proof.go_etcd_io.etcd.client.v3.WatchResumeSrv
public import Proof.go_etcd_io.etcd.client.v3.WatchEpoch
public import Proof.go_etcd_io.etcd.client.v3.InvLessor

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.api.v3 go_etcd_io.etcd.cache.v3 client



section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

theorem watchGRPCStream.run.wp_proof
    (wp_newWC : watchGRPCStream.newWatchClient.spec (GF := GF) (hG := hG))
    (wp_nextResume : watchGRPCStream.nextResume.spec (GF := GF) (hG := hG))
    (wp_dispatch : watchGRPCStream.dispatchEvent.spec (GF := GF) (hG := hG))
    (wp_addSub : watchGRPCStream.addSubstream.spec (GF := GF) (hG := hG))
    (wp_closeSub : watchGRPCStream.closeSubstream.spec (GF := GF) (hG := hG))
    (wp_join : watchGRPCStream.joinSubstreams.spec (GF := GF) (hG := hG))
    (wp_serveSub : watchGRPCStream.serveSubstream.spec (GF := GF) (hG := hG))
    (wp_bufLogger : watchGRPCStream.newWatcherStreamBufLogger.spec (GF := GF) (hG := hG))
    (wp_toPB : watchRequest.toPB.spec (GF := GF) (hG := hG))
    (wp_ptoPB : progressRequest.toPB.spec (GF := GF) (hG := hG))
    (wp_closeStream : watcher.closeStream.spec (GF := GF) (hG := hG))
    (wp_isHaltErr : isHaltErr.spec (GF := GF) (hG := hG))
    (wp_Debug : zap.Logger.Debug.spec (GF := GF) (hG := hG))
    (wp_zapError : zap.Error.spec (GF := GF) (hG := hG))
    (wp_zapInt64 : zap.Int64.spec (GF := GF) (hG := hG))
    (wp_ctxErr : ContextError.spec (GF := GF) (hG := hG))
    (wp_isStatus : errors.IsStatusErr.spec (GF := GF) (hG := hG))
    (wp_backoff : watchGRPCStream.backoffIfUnavailable.spec (GF := GF) (hG := hG)) :
    watchGRPCStream.run.spec (GF := GF) (hG := hG) := by
  -- the proof before G2: `git show 8527537fba:Proof/go_etcd_io/etcd/client/v3/watchGRPCStream__run.lean`
  sorry -- G2: re-prove after freeze

end proof

end EtcdGrove
end Perennial
