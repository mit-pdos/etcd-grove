/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/NewServer.lean`. Lean-first (no Rocq
counterpart); placed at the server-construction unit's stage N0 (2026-10-16), unit N1's to prove
(D13 and D13a-d, `notes/decisions.md`). The hypotheses are the callees' specs in the order of
`etc/link-lean-first-server.txt` (`NewServer: …`); raft's node methods are for the raft wrapper's
composition (`raftNode_of_StartNode`, `NodeStart.lean`, restated with the environment chosen
before the call: N1).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.NewServer
public import Spec.github_com.prometheus.client_golang.prometheus.GaugeVec__With
public import Spec.go_etcd_io.etcd.client.pkg.v3.types.ID__String
public import Spec.go_etcd_io.etcd.client.pkg.v3.types.URLs__StringSlice
public import Spec.go_etcd_io.etcd.pkg.v3.idutil.NewGenerator
public import Spec.go_etcd_io.etcd.pkg.v3.notify.NewNotifier
public import Spec.go_etcd_io.etcd.server.v3.auth.NewAuthStore
public import Spec.go_etcd_io.etcd.server.v3.auth.NewTokenProvider
public import Spec.go_etcd_io.etcd.server.v3.config.ServerConfig__PeerDialTimeout
public import Spec.go_etcd_io.etcd.server.v3.config.ServerConfig__ReqTimeout
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__FeatureEnabled
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__Logger
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__NewUberApplier
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__getTxPostLockInsideApplyHook
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__restoreAlarms
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.addFeatureGateMetrics
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.membership.RaftCluster__ID
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.membership.RaftCluster__Members
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.membership.RaftCluster__SetVersionChangedNotifier
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.membership.RaftCluster__String
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.Transport__AddPeer
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.Transport__AddRemote
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.Transport__Start
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v2stats.NewLeaderStats
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v2stats.NewServerStats
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3compactor.New
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.bootstrappedRaft__newRaftNode
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.newCorruptionChecker
public import Spec.go_etcd_io.etcd.server.v3.lease.NewLessor
public import Spec.go_etcd_io.etcd.server.v3.storage.backend.backend__SetTxPostLockInsideApplyHook
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.New
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.store__HashStorage
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.watchableStore__Close
public import Spec.go_etcd_io.etcd.server.v3.storage.schema.NewAuthBackend
public import Spec.go_etcd_io.raft.v3.node__Advance
public import Spec.go_etcd_io.raft.v3.node__ReadIndex
public import Spec.go_etcd_io.raft.v3.node__Ready
public import Spec.go_etcd_io.raft.v3.node__Tick
public import Spec.go_uber_org.zap.Error
public import Spec.go_uber_org.zap.Logger__Error
public import Spec.go_uber_org.zap.Logger__Info
public import Spec.go_uber_org.zap.Logger__Warn
public import Spec.math.Ceil
public import Spec.time.Duration__Seconds
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.BuildAlloc
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.BuildGap

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.raft.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
variable [MemStorReg GF]

theorem NewServer.wp_proof
    (h0 : zap.Logger.Error.spec (GF := GF) (hG := hG))
    (h1 : zap.Error.spec (GF := GF) (hG := hG))
    (h2 : zap.Logger.Info.spec (GF := GF) (hG := hG))
    (h3 : zap.Logger.Warn.spec (GF := GF) (hG := hG))
    (h4 : v2stats.NewServerStats.spec (GF := GF) (hG := hG))
    (h5 : membership.RaftCluster.String.spec (GF := GF) (hG := hG))
    (h6 : v2stats.NewLeaderStats.spec (GF := GF) (hG := hG))
    (h7 : types.ID.String.spec (GF := GF) (hG := hG))
    (h8 : bootstrappedRaft.newRaftNode.spec (GF := GF) (hG := hG))
    (h9 : node.Ready.spec (GF := GF) (hG := hG))
    (h10 : node.Advance.spec (GF := GF) (hG := hG))
    (h11 : node.Tick.spec (GF := GF) (hG := hG))
    (h12 : node.ReadIndex.spec (GF := GF) (hG := hG))
    (h13 : types.URLs.StringSlice.spec (GF := GF) (hG := hG))
    (h14 : idutil.NewGenerator.spec (GF := GF) (hG := hG))
    (h15 : notify.NewNotifier.spec (GF := GF) (hG := hG))
    (h16 : addFeatureGateMetrics.spec (GF := GF) (hG := hG))
    (h17 : prometheus.GaugeVec.With.spec (GF := GF) (hG := hG))
    (h18 : membership.RaftCluster.SetVersionChangedNotifier.spec (GF := GF) (hG := hG))
    (h19 : EtcdServer.Logger.spec (GF := GF) (hG := hG))
    (h20 : config.ServerConfig.ReqTimeout.spec (GF := GF) (hG := hG))
    (h21 : EtcdServer.FeatureEnabled.spec (GF := GF) (hG := hG))
    (h22 : time.Duration.Seconds.spec (GF := GF) (hG := hG))
    (h23 : math.Ceil.spec (GF := GF) (hG := hG))
    (h24 : lease.NewLessor.spec (GF := GF) (hG := hG))
    (h25 : auth.NewTokenProvider.spec (GF := GF) (hG := hG))
    (h26 : mvcc.New.spec (GF := GF) (hG := hG))
    (h27 : newCorruptionChecker.spec (GF := GF) (hG := hG))
    (h28 : mvcc.store.HashStorage.spec (GF := GF) (hG := hG))
    (h29 : schema.NewAuthBackend.spec (GF := GF) (hG := hG))
    (h30 : auth.NewAuthStore.spec (GF := GF) (hG := hG))
    (h31 : v3compactor.New.spec (GF := GF) (hG := hG))
    (h32 : EtcdServer.restoreAlarms.spec (GF := GF) (hG := hG))
    (h33 : EtcdServer.NewUberApplier.spec (GF := GF) (hG := hG))
    (h34 : EtcdServer.getTxPostLockInsideApplyHook.spec (GF := GF) (hG := hG))
    (h35 : backend.backend.SetTxPostLockInsideApplyHook.spec (GF := GF) (hG := hG))
    (h36 : config.ServerConfig.PeerDialTimeout.spec (GF := GF) (hG := hG))
    (h37 : membership.RaftCluster.ID.spec (GF := GF) (hG := hG))
    (h38 : rafthttp.Transport.Start.spec (GF := GF) (hG := hG))
    (h39 : rafthttp.Transport.AddRemote.spec (GF := GF) (hG := hG))
    (h40 : membership.RaftCluster.Members.spec (GF := GF) (hG := hG))
    (h41 : rafthttp.Transport.AddPeer.spec (GF := GF) (hG := hG))
    (h42 : mvcc.watchableStore.Close.spec (GF := GF) (hG := hG)) :
    NewServer.spec (GF := GF) (hG := hG) := by
  sorry

end proof

end EtcdGrove
end Perennial
