/-
**`putgetc`** (M2, 2026-10-27, `notes/m2-plan.md`): putget's file, for putget with the
auto-compactor on (`common.StartCompactingServer`, revision mode, retention 1); putget's history
below is the original's.

`Main`'s callees linked (item 9, 2026-10-18), by hand: `putgetc.Main.wp_proof` applied to their
linked results in the examples' shared start's `Link.lean` (`common`'s, over the server's, v3rpc's
and the client's, since 2026-10-22, D33), `context`'s, and to the trust-boundary axiom of
`zap.NewNop`, which no `Link.lean` links yet. `etc/gen-link.py` has no
mode combining several packages' Links (each mode links one package, with `@` callees of the
Links it imports under one namespace); a `--putgetc` mode is the follow-up if more of the example
is linked. `Results.lean` restates it.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.putgetc.Main
public import Proof.github_com.mit_pdos.etcd_grove.examples.common.Link
public import Proof.github_com.mit_pdos.etcd_grove.examples.common.StartCompactingServer
public import Proof.go_uber_org.zap.NewNop
public import Perennial.Proof.context.Link
public import Proof.context.Link
public import Proof.context.WithTimeoutBackground

@[expose] public section

set_option pp.fullNames true
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section results
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.putgetc.Assumptions]

/-- `StartCompactingServer`, over `newServer`'s compacting variant (`specCompact`) and
`NewServer`'s (`NewServer.specCompact`, M2's S4: `NewServer.wp_proofCompact`, over `NewServer`'s
linked callees and the compacting server's own: the compacting store's backend contract's, the
store's `Rev` and the server's `Compact`), linked by hand: `etc/gen-link.py` links a function's one
`wp_proof`. -/
theorem putgetc.wp_StartCompactingServer [go_etcd_io.etcd.cache.v3.Assumptions]
    [Float64ToInt64Semantics] :
    common.StartCompactingServer.spec (GF := GF) (hG := hG) :=
  common.StartCompactingServer.wp_proof
    (common.newServer.wp_proofCompact common.features.wp_NewDefaultServerFeatureGate
      (fun {_} => NewServer.wp_proofCompact zap.Logger.wp_Error zap.wp_Error zap.Logger.wp_Info zap.Logger.wp_Warn v2stats.wp_NewServerStats membership.RaftCluster.wp_String v2stats.wp_NewLeaderStats types.ID.wp_String_ptr bootstrappedRaft.wp_newRaftNode srvApi_wp_Ready srvApi_wp_Advance srvApi_wp_Stop srvApi_wp_Tick srvApi_wp_ReadIndex types.URLs.wp_StringSlice idutil.wp_NewGenerator notify.wp_NewNotifier wp_addFeatureGateMetrics prometheus.GaugeVec.wp_With membership.RaftCluster.wp_SetVersionChangedNotifier EtcdServer.wp_Logger config.ServerConfig.wp_ReqTimeout EtcdServer.wp_FeatureEnabled time.Duration.wp_Seconds_ptr math.wp_Ceil lease.wp_NewLessor auth.wp_NewTokenProvider mvcc.wp_New wp_newCorruptionChecker mvcc.store.wp_HashStorage schema.wp_NewAuthBackend auth.wp_NewAuthStore v3compactor.wp_New EtcdServer.wp_restoreAlarms EtcdServer.wp_NewUberApplier EtcdServer.wp_getTxPostLockInsideApplyHook backend.backend.wp_SetTxPostLockInsideApplyHook config.ServerConfig.wp_PeerDialTimeout membership.RaftCluster.wp_ID rafthttp.Transport.wp_Start rafthttp.Transport.wp_AddRemote rafthttp.Transport.wp_AddPeer mvcc.watchableStore.wp_Close schema.bucket.wp_ID schema.bucket.wp_Name schema.bucket.wp_IsSafeRangeBucket lease.lessor.wp_GetLease lease.lessor.wp_Attach lease.lessor.wp_Detach lease.lessor.wp_SetRangeDeleter lease.lessor.wp_Lookup lease.lessor.wp_Grant lease.lessor.wp_Checkpoint lease.Lease.wp_TTL lease.lessor.wp_Promote lease.lessor.wp_Demote lease.lessor.wp_ExpiredLeasesC backend.backend.wp_ConcurrentReadTx backend.backend.wp_ReadTx backend.backend.wp_BatchTx backend.backend.wp_ForceCommit backend.backend.wp_Size backend.backend.wp_SizeInUse backend.concurrentReadTx.wp_RLock backend.concurrentReadTx.wp_RUnlock backend.concurrentReadTx.wp_UnsafeRange backend.readTx.wp_RLock backend.readTx.wp_RUnlock backend.readTx.wp_UnsafeRange backend.batchTxBuffered.wp_LockInsideApply backend.batchTxBuffered.wp_LockOutsideApply backend.batchTxBuffered.wp_UnsafeSeqPut backend.batchTxBuffered.wp_Unlock backend.batchTxBuffered.wp_UnsafeRange backend.batchTxBuffered.wp_UnsafeCreateBucket srvApi_wp_Propose EtcdServer.wp_MemberID EtcdServer.wp_Leader EtcdServer.wp_Term EtcdServer.wp_ForceSnapshot consistentIndex.wp_ConsistentIndex EtcdServer.wp_ClusterVersion srvApi_wp_MemSnapshot srvApi_wp_ApplyConfChange srvApi_wp_MemInitialState srvApi_wp_MemLastIndex srvApi_wp_MemFirstIndex srvApi_wp_MemTerm srvApi_wp_MemEntries srvApi_wp_Step srvApi_wp_ReportUnreachable srvApi_wp_ReportSnapshot EtcdServer.wp_Process EtcdServer.wp_IsIDRemoved EtcdServer.wp_ReportUnreachable EtcdServer.wp_ReportSnapshot backend.batchTxBuffered.wp_UnsafeDelete
        backend.backend.wp_LockForSafeRangeDelete backend.backend.wp_UnlockForSafeRangeDelete
        backend.batchTxBuffered.wp_UnsafePut mvcc.store.wp_Rev EtcdServer.wp_Compact))
    EtcdServer.wp_Start

/-- **The adequacy example's `Main` does not panic** (see the file header;
`Spec/github_com/mit_pdos/etcd_grove/examples/putgetc/Main.lean`), under the semantic premises of
its callees' linked results: `int64(f)` of a `float64` (`Float64ToInt64Semantics`, the server's)
and the client's `dialWithBalancer` body (`DialWithBalancerBody`). -/
theorem putgetc.wp_Main [Float64ToInt64Semantics] [go_etcd_io.etcd.client.v3.DialWithBalancerBody] :
    putgetc.Main.spec (GF := GF) (hG := hG) :=
  putgetc.Main.wp_proof zap.NewNop.wp_proof putgetc.wp_StartCompactingServer common.wp_Serve
    common.wp_NewClient context.wp_Background context.WithTimeoutBackground.wp_proof
    context.wp_ErrAny

end results


end EtcdGrove
end Perennial
