-- The copy for the part `KvRaft/` of `RaftNoAx/Proof/go_etcd_io/raft/v3/RawNode__Step.lean` (etc/copy-part.py; rerun it, do not edit).
/- Lean-first (no Rocq counterpart).
raft v3.7 (2026-10-16, stage R5): the message is a pointer, its type and sender read by the getters
(`Message.GetType`/`GetFrom` on `msgIn`), and passed to `raft.Step` for good.

(2026-10-20, D22 S-c) A `MsgSnap` too: `raft.Step`'s snapshot clause (`SnapStep`, `SnapCfgOut`)
rebuilds the node at the configuration the restore installs (static: the ghost state's voters, not
joint, `GMode.SnapOk`), with the pending snapshot recorded in `RNState.psnap`.

(#33 S4, P-raft-3) The proof is the strengthened triple's, `RawNode.Step.wp_absProof`
(`RawNode__StepAbs.lean`, where this file's proof moved, over `ownRawNodeAt`); the old spec is its
corollary (`RawNode.Step.spec_of_abs`, `RawNodeSpecOfAbs.lean`). One proof.
-/
module

public import KvRaft.Spec.go_etcd_io.raft.v3.RawNode__Step
public import KvRaft.Spec.go_etcd_io.raft.v3.raft__Step
public import KvRaft.Spec.go_etcd_io.raft.v3.raftpb.Message__GetType
public import KvRaft.Spec.go_etcd_io.raft.v3.raftpb.Message__GetFrom
public import KvRaft.Spec.go_etcd_io.raft.v3.IsLocalMsg
public import KvRaft.Spec.go_etcd_io.raft.v3.IsResponseMsg
public import KvRaft.Spec.go_etcd_io.raft.v3.IsLocalMsgTarget
public import KvRaft.Proof.go_etcd_io.raft.v3.RawNode__StepAbs
public import KvRaft.Proof.go_etcd_io.raft.v3.RawNodeSpecOfAbs

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

/-- The two guards, then `raft.Step` (`RawNode.Step.wp_absProof` outside the scope). -/
theorem RawNode.Step.wp_proof
    (wp_IsResponseMsg : IsResponseMsg.spec (GF := GF) (hG := hG))
    (wp_IsLocalMsg : IsLocalMsg.spec (GF := GF) (hG := hG))
    (wp_IsLocalMsgTarget : IsLocalMsgTarget.spec (GF := GF) (hG := hG))
    (wp_raft_Step : raft.Step.spec (GF := GF) (hG := hG))
    (wp_GetType : raftpb.Message.GetType.spec (GF := GF) (hG := hG))
    (wp_GetFrom : raftpb.Message.GetFrom.spec (GF := GF) (hG := hG)) :
    RawNode.Step.spec (GF := GF) (hG := hG) :=
  RawNode.Step.spec_of_abs (RawNode.Step.wp_absProof wp_IsResponseMsg wp_IsLocalMsg
    wp_IsLocalMsgTarget wp_raft_Step wp_GetType wp_GetFrom)

end proof

end EtcdGrove
end Perennial
