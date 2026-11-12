/- Lean-first (no Rocq counterpart), 2026-10-13: reconfiguration stage D.

raft v3.7 (stage R4): `cc` is a `*pb.ConfChangeV2` (`ownConfChangeV2`), read by `LeaveJoint`/`EnterJoint`
(pointer methods with specs, no longer unfolded); `cc.Changes...` opens it for the field load and
folds it back after the changer. -/
module

public import Proof.go_etcd_io.raft.v3.TracedApplyConfChange

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- `r.applyConfChange(cc)`, untraced: the untraced instance (`spec_of_tracedSpec`) of the one proof,
`raft.applyConfChange.tracedSpec_proof` (`TracedApplyConfChange.lean`; 2026-11-12, trace-check step 4:
until then the proof was here, the same with the struct opened by `ownRaftPhysC_retrack`). -/
theorem raft.applyConfChange.wp_proof
    (wp_raftLog_lastIndex : raftLog.lastIndex.spec (GF := GF) (hG := hG))
    (wp_ConfChangeV2_LeaveJoint : raftpb.ConfChangeV2.LeaveJoint.spec (GF := GF) (hG := hG))
    (wp_ConfChangeV2_EnterJoint : raftpb.ConfChangeV2.EnterJoint.spec (GF := GF) (hG := hG))
    (wp_Changer_LeaveJoint : confchange.Changer.LeaveJoint.spec (GF := GF) (hG := hG))
    (wp_Changer_EnterJoint : confchange.Changer.EnterJoint.spec (GF := GF) (hG := hG))
    (wp_Changer_Simple : confchange.Changer.Simple.spec (GF := GF) (hG := hG))
    (wp_raft_switchToConfig : raft.switchToConfig.spec (GF := GF) (hG := hG)) :
    raft.applyConfChange.spec (GF := GF) (hG := hG) :=
  raft.applyConfChange.spec_of_tracedSpec
    (raft.applyConfChange.tracedSpec_proof wp_raftLog_lastIndex wp_ConfChangeV2_LeaveJoint
      wp_ConfChangeV2_EnterJoint wp_Changer_LeaveJoint wp_Changer_EnterJoint wp_Changer_Simple
      wp_raft_switchToConfig)

end proof

end EtcdGrove
end Perennial
