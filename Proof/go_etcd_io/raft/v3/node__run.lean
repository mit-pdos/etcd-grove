/- Lean-first (no Rocq counterpart).

**`node.run`, both modes: the one proof** (2026-11-12, trace-check step 5). `node.run.spec` is step 4's
gated statement (in place since step 5), proved by `node.run.gated_of` (`node__run_gated.lean`) from its
callees' specs, the traced step's assembly `stepBundle_traced` (a closed theorem) and step 4's `hCC`
(`raft.applyConfChange.tracedSpec`, an instance of `raft.applyConfChange.spec`). Until step 5 this file
held the untraced proof (raft v3.7 stage R5, the D22 snapshot loans, durability stage II (n)), which
`node__run_gated.lean` generalized to both modes and which is gone, so that `run` has one proof.
-/
module

public import Proof.go_etcd_io.raft.v3.node__run_gated
public import Proof.go_etcd_io.raft.v3.TracedRaftStepBundle
public import Proof.go_etcd_io.raft.v3.TracedApplyConfChange

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- **`n.run()`, both modes** (see the file header). -/
theorem node.run.wp_proof
    (wp_RawNode_HasReady : RawNode.HasReady.spec (GF := GF) (hG := hG))
    (wp_RawNode_readyWithoutAccept : RawNode.readyWithoutAccept.spec (GF := GF) (hG := hG))
    (wp_RawNode_acceptReady : RawNode.acceptReady.spec (GF := GF) (hG := hG))
    (wp_RawNode_Advance : RawNode.Advance.spec (GF := GF) (hG := hG))
    (wp_RawNode_Tick : RawNode.Tick.spec (GF := GF) (hG := hG))
    (wp_tickElection : raft.tickElection.spec (GF := GF) (hG := hG))
    (wp_tickHeartbeat : raft.tickHeartbeat.spec (GF := GF) (hG := hG))
    (wp_raft_Step : raft.Step.spec (GF := GF) (hG := hG))
    (wp_raft_hasLeader : raft.hasLeader.spec (GF := GF) (hG := hG))
    (wp_IsResponseMsg : IsResponseMsg.spec (GF := GF) (hG := hG))
    (wp_IsLocalMsgTarget : IsLocalMsgTarget.spec (GF := GF) (hG := hG))
    (wp_raft_applyConfChange : raft.applyConfChange.spec (GF := GF) (hG := hG))
    (wp_GetType : raftpb.Message.GetType.spec (GF := GF) (hG := hG))
    (wp_GetFrom : raftpb.Message.GetFrom.spec (GF := GF) (hG := hG))
    (wp_getStatus : getStatus.spec (GF := GF) (hG := hG)) :
    node.run.spec (GF := GF) (hG := hG) :=
  node.run.gated_of wp_RawNode_HasReady wp_RawNode_readyWithoutAccept wp_RawNode_acceptReady
    wp_RawNode_Advance wp_RawNode_Tick wp_tickElection wp_tickHeartbeat wp_raft_Step stepBundle_traced
    wp_raft_hasLeader wp_IsResponseMsg wp_IsLocalMsgTarget
    (raft.applyConfChange.tracedSpec_of_spec wp_raft_applyConfChange) wp_GetType wp_GetFrom wp_getStatus

end proof

end EtcdGrove
end Perennial
