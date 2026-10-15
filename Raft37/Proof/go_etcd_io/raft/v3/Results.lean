/-
The raft v3.7 results ported so far into the parallel tree `Raft37/` (stage R0 of the
retarget, `notes/raft-retarget-plan.md`): `quorum`, `tracker` and `slices.Sort`; since stage R1
`raftpb` (the getters, `Enum`, `Ensure*`, the conf-change codec, `ConfState.Equivalent`) and the
nine protobuf-go axioms (`proto.*`, the trust boundary); since stage R2 `confchange` (with
etcd-grove's `fmt.Errorf` axiom and `raftpb.ConfChangeType.String` at the trust boundary), as
`Proof/go_etcd_io/raft/v3/Link.lean` links them for the verified raft. `#print axioms` of each
is its trust base (in the build log); `etc/tcb-report.py --collection
etc/tcb-collections/raft37.txt` reports on them. The tree replaces the old raft proof's when
it reaches its results (`Proof/go_etcd_io/raft/v3/Results.lean`).

Since stage R1 also the protocol model's results (`Protocol/ResultsDyn.lean`, `Protocol/Facts.lean`:
safety under reconfiguration, election safety, the read index, log matching, state machine
safety, leader completeness), ported from the old tree by a type rename; and the model-level
step lemmas (`StepGhostMode`) are imported so the build checks them.
-/
module

public import Raft37.Proof.go_etcd_io.raft.v3.Link
-- the protocol model's results (stage R1: the model ported)
public import Raft37.Proof.go_etcd_io.raft.v3.Protocol.ResultsDyn
public import Raft37.Proof.go_etcd_io.raft.v3.Protocol.Facts
public import Raft37.Proof.go_etcd_io.raft.v3.StepGhostMode

@[expose] public section

namespace Perennial
namespace EtcdGrove

#print axioms slices.wp_Sort
#print axioms quorum.MajorityConfig.wp_CommittedIndex
#print axioms quorum.JointConfig.wp_CommittedIndex
#print axioms quorum.JointConfig.wp_IDs
#print axioms quorum.MajorityConfig.wp_VoteResult
#print axioms quorum.JointConfig.wp_VoteResult
#print axioms quorum.MajorityConfig.wp_Slice
#print axioms quorum.mapAckIndexer.wp_AckedIndex
#print axioms tracker.Config.wp_Clone
#print axioms tracker.Inflights.wp_Full
#print axioms tracker.Inflights.wp_grow
#print axioms tracker.Inflights.wp_Add
#print axioms tracker.Inflights.wp_Clone
#print axioms tracker.Inflights.wp_Count
#print axioms tracker.Inflights.wp_FreeLE
#print axioms tracker.Inflights.wp_reset
#print axioms tracker.wp_MakeProgressTracker
#print axioms tracker.wp_NewInflights
#print axioms tracker.matchAckIndexer.wp_AckedIndex
#print axioms tracker.ProgressTracker.wp_Committed
#print axioms tracker.ProgressTracker.wp_ConfState
#print axioms tracker.ProgressTracker.wp_IsSingleton
#print axioms tracker.ProgressTracker.wp_LearnerNodes
#print axioms tracker.ProgressTracker.wp_Visit
#print axioms tracker.ProgressTracker.wp_QuorumActive
#print axioms tracker.ProgressTracker.wp_RecordVote
#print axioms tracker.ProgressTracker.wp_ResetVotes
#print axioms tracker.ProgressTracker.wp_TallyVotes
#print axioms tracker.ProgressTracker.wp_VoterNodes
#print axioms tracker.Progress.wp_ResetState
#print axioms tracker.Progress.wp_BecomeProbe
#print axioms tracker.Progress.wp_BecomeReplicate
#print axioms tracker.Progress.wp_BecomeSnapshot
#print axioms tracker.Progress.wp_CanBumpCommit
#print axioms tracker.Progress.wp_IsPaused
#print axioms tracker.Progress.wp_MaybeDecrTo
#print axioms tracker.Progress.wp_MaybeUpdate
#print axioms tracker.Progress.wp_SentCommit
#print axioms tracker.Progress.wp_SentEntries

-- raftpb (stage R1) and the protobuf trust boundary it rests on
#print axioms proto.wp_CloneConfState
#print axioms proto.wp_CloneEntry
#print axioms proto.wp_CloneSnapshot
#print axioms proto.wp_EqualConfState
#print axioms proto.wp_MarshalConfChange
#print axioms proto.wp_MarshalConfChangeV2
#print axioms proto.wp_SizeEntry
#print axioms proto.wp_UnmarshalConfChange
#print axioms proto.wp_UnmarshalConfChangeV2
#print axioms raftpb.ConfChangeSingle.wp_GetNodeId
#print axioms raftpb.ConfChangeSingle.wp_GetType
#print axioms raftpb.ConfChangeTransition.wp_Enum
#print axioms raftpb.ConfChangeType.wp_Enum
#print axioms raftpb.ConfChangeV2.wp_AsV1
#print axioms raftpb.ConfChangeV2.wp_AsV2
#print axioms raftpb.ConfChangeV2.wp_GetTransition
#print axioms raftpb.ConfChangeV2.wp_EnterJoint
#print axioms raftpb.ConfChangeV2.wp_GetChanges
#print axioms raftpb.ConfChangeV2.wp_GetContext
#print axioms raftpb.ConfChangeV2.wp_LeaveJoint
#print axioms raftpb.ConfChange.wp_AsV1
#print axioms raftpb.ConfChange.wp_GetType
#print axioms raftpb.ConfChange.wp_GetNodeId
#print axioms raftpb.ConfChange.wp_AsV2
#print axioms raftpb.ConfChange.wp_GetContext
#print axioms raftpb.ConfChange.wp_GetId
#print axioms raftpb.ConfState.wp_GetAutoLeave
#print axioms raftpb.ConfState.wp_Equivalent
#print axioms raftpb.ConfState.wp_GetLearners
#print axioms raftpb.ConfState.wp_GetLearnersNext
#print axioms raftpb.ConfState.wp_GetVoters
#print axioms raftpb.ConfState.wp_GetVotersOutgoing
#print axioms raftpb.wp_EnsureConfState
#print axioms raftpb.wp_EnsureSnapshotMetadata
#print axioms raftpb.wp_EnsureSnapshot
#print axioms raftpb.EntryType.wp_Enum
#print axioms raftpb.Entry.wp_GetData
#print axioms raftpb.Entry.wp_GetIndex
#print axioms raftpb.Entry.wp_GetTerm
#print axioms raftpb.Entry.wp_GetType
#print axioms raftpb.HardState.wp_GetCommit
#print axioms raftpb.HardState.wp_GetTerm
#print axioms raftpb.HardState.wp_GetVote
#print axioms raftpb.wp_MarshalConfChange
#print axioms raftpb.MessageType.wp_Enum
#print axioms raftpb.Message.wp_GetCommit
#print axioms raftpb.Message.wp_GetContext
#print axioms raftpb.Message.wp_GetEntries
#print axioms raftpb.Message.wp_GetFrom
#print axioms raftpb.Message.wp_GetIndex
#print axioms raftpb.Message.wp_GetLogTerm
#print axioms raftpb.Message.wp_GetReject
#print axioms raftpb.Message.wp_GetRejectHint
#print axioms raftpb.Message.wp_GetResponses
#print axioms raftpb.Message.wp_GetSnapshot
#print axioms raftpb.Message.wp_GetTerm
#print axioms raftpb.Message.wp_GetTo
#print axioms raftpb.Message.wp_GetType
#print axioms raftpb.Message.wp_GetVote
#print axioms raftpb.SnapshotMetadata.wp_GetConfState
#print axioms raftpb.SnapshotMetadata.wp_GetIndex
#print axioms raftpb.SnapshotMetadata.wp_GetTerm
#print axioms raftpb.Snapshot.wp_GetData
#print axioms raftpb.Snapshot.wp_GetMetadata

-- confchange (stage R2), with etcd-grove's `fmt.Errorf` and `ConfChangeType.String` axioms
#print axioms confchange.wp_incoming
#print axioms confchange.wp_outgoing
#print axioms confchange.wp_outgoingPtr
#print axioms confchange.wp_joint
#print axioms confchange.wp_nilAwareAdd
#print axioms confchange.wp_nilAwareDelete
#print axioms confchange.wp_symdiff
#print axioms confchange.wp_checkInvariants
#print axioms confchange.wp_checkAndReturn
#print axioms confchange.Changer.wp_checkAndCopy
#print axioms confchange.Changer.wp_err
#print axioms confchange.Changer.wp_initProgress
#print axioms confchange.Changer.wp_remove
#print axioms confchange.Changer.wp_makeVoter
#print axioms confchange.Changer.wp_makeLearner
#print axioms raftpb.ConfChangeType.wp_String
#print axioms confchange.Changer.wp_apply
#print axioms confchange.Changer.wp_Simple
#print axioms confchange.Changer.wp_EnterJoint
#print axioms confchange.Changer.wp_LeaveJoint
#print axioms confchange.wp_toConfChangeSingle
#print axioms confchange.wp_chain
#print axioms confchange.wp_Restore

-- the protocol model (stage R1)
#print axioms raft_dyn_alloc
#print axioms raft_dyn_committed_agree
#print axioms raft_dyn_election_safety
#print axioms raft_dyn_read_states
#print axioms raft_dyn_read_index
#print axioms log_matching
#print axioms state_machine_safety
#print axioms leader_completeness

end EtcdGrove
end Perennial
