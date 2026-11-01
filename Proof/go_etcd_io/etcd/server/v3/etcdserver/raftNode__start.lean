/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/raftNode__start.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.raftNode__start
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvRaftLoop
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.RaftLoopFreeze
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.raftNode__tick
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.raftNode__processMessages
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.updateCommittedIndex
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.raftNode__onStop
public import Spec.go_etcd_io.raft.v3.IsEmptySnap
public import Spec.go_etcd_io.raft.v3.IsEmptyHardState
public import Spec.go_etcd_io.raft.v3.raftpb.HardState__GetCommit
public import Spec.go_etcd_io.raft.v3.raftpb.HardState__GetTerm
public import Spec.go_etcd_io.raft.v3.raftpb.Entry__GetType
public import Spec.google_golang_org.protobuf.proto.Clone
public import Spec.go_uber_org.zap.Error
public import Spec.go_uber_org.zap.Logger__Fatal
public import Spec.go_uber_org.zap.Duration
public import Spec.go_uber_org.zap.Logger__Warn
public import Proof.go_etcd_io.raft.v3.Linked

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open RaftLink

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

-- (2026-10-22) the unused-variables linter walks the proof's info tree: 8s of this module's CPU
set_option linter.unusedVariables false in
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem raftNode.start.wp_proof
    (wp_tick : raftNode.tick.spec (GF := GF) (hG := hG))
    (wp_processMessages : raftNode.processMessages.spec (GF := GF) (hG := hG))
    (wp_updateCommittedIndex : updateCommittedIndex.spec (GF := GF) (hG := hG))
    (wp_onStop : raftNode.onStop.spec (GF := GF) (hG := hG))
    (wp_IsEmptySnap : IsEmptySnap.spec (GF := GF) (hG := hG))
    (wp_IsEmptyHardState : IsEmptyHardState.spec (GF := GF) (hG := hG))
    (wp_GetCommit : raftpb.HardState.GetCommit.spec (GF := GF) (hG := hG))
    (wp_GetTerm : raftpb.HardState.GetTerm.spec (GF := GF) (hG := hG))
    (wp_GetType : raftpb.Entry.GetType.spec (GF := GF) (hG := hG))
    (wp_Clone : proto.Clone.spec (GF := GF) (hG := hG))
    (wp_Error : zap.Error.spec (GF := GF) (hG := hG))
    (wp_Fatal : zap.Logger.Fatal.spec (GF := GF) (hG := hG))
    (wp_Duration : zap.Duration.spec (GF := GF) (hG := hG))
    (wp_Warn : zap.Logger.Warn.spec (GF := GF) (hG := hG)) :
    raftNode.start.spec (GF := GF) (hG := hG) := by
  -- PORT(durability stage II): a definition or statement it uses changed (durability stage I-2..I-8)
  sorry

end proof

end EtcdGrove
end Perennial
