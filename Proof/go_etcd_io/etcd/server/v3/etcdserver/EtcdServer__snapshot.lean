/-
`EtcdServer.snapshot` (2026-10-30, the repair: a theorem, until then the trust-boundary axiom; its
proof is `SnapTakeProof.lean`'s `wp_proof_full`, proved on lean over the old storage token, to be
rewired: SNAPSHOT-SORRY).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__snapshot
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__Logger
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__MemberID
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__KV
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.verifyConsistentIndexIsLatest
public import Spec.go_etcd_io.etcd.server.v3.storage.storage__Release
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.cindex.consistentIndex__ConsistentIndex
public import Spec.go_etcd_io.raft.v3.MemoryStorage__CreateSnapshot
public import Spec.go_etcd_io.raft.v3.raftpb.SnapshotMetadata__GetIndex
public import Spec.go_etcd_io.etcd.client.pkg.v3.types.ID__String
public import Spec.errors.Is
public import Spec.go_uber_org.zap.Logger__Info
public import Spec.go_uber_org.zap.Uint64
public import Spec.go_uber_org.zap.String
public import Spec.go_uber_org.zap.Bool

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

theorem EtcdServer.snapshot.wp_proof
    (hLg : EtcdServer.Logger.spec (GF := GF) (hG := hG))
    (hMID : EtcdServer.MemberID.spec (GF := GF) (hG := hG))
    (hIDS : types.ID.String.spec (GF := GF) (hG := hG))
    (hKV : EtcdServer.KV.spec (GF := GF) (hG := hG))
    (hCS : MemoryStorage.CreateSnapshot.spec (GF := GF) (hG := hG))
    (hIs : errors.Is.spec (GF := GF) (hG := hG))
    (hCI : consistentIndex.ConsistentIndex.spec (GF := GF) (hG := hG))
    (hVer : verifyConsistentIndexIsLatest.spec (GF := GF) (hG := hG))
    (hRel : storage.storage.Release.spec (GF := GF) (hG := hG))
    (hGI : raftpb.SnapshotMetadata.GetIndex.spec (GF := GF) (hG := hG))
    (hInfo : zap.Logger.Info.spec (GF := GF) (hG := hG))
    (hU64 : zap.Uint64.spec (GF := GF) (hG := hG))
    (hStr : zap.String.spec (GF := GF) (hG := hG))
    (hBool : zap.Bool.spec (GF := GF) (hG := hG)) :
    EtcdServer.snapshot.spec (GF := GF) (hG := hG) := by
  -- SNAPSHOT-SORRY: `SnapTakeProof.lean`'s `wp_proof_full`, rewired: `CreateSnapshot` over
  -- `srvSnapStor` (`snapshotCert_make` in the registry, `snapshotCert_valid` for `J.SV`, `storDL`
  -- for `J.DL`, the frozen entry of `srvSnapState`), `memSnapLb ai` after
  sorry

end proof

end EtcdGrove
end Perennial
