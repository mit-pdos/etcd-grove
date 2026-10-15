/-
The raft v3.7 results ported so far into the parallel tree `Raft37/` (stage R0 of the
retarget, `notes/raft-retarget-plan.md`): `quorum`, `tracker` and `slices.Sort`; since stage R1
`raftpb` (the getters, `Enum`, `Ensure*`, the conf-change codec, `ConfState.Equivalent`) and the
nine protobuf-go axioms (`proto.*`, the trust boundary); since stage R2 `confchange` (with
etcd-grove's `fmt.Errorf` axiom and `raftpb.ConfChangeType.String` at the trust boundary); since
stage R3 the log layer (`unstable`, `raftLog`, `MemoryStorage`, the size helpers, over read-only
entries) and `MemoryStorage`'s instance of the `Storage` contract, as
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
-- `MemoryStorage` meets the `Storage` contract (stage R3)
public import Raft37.Proof.go_etcd_io.raft.v3.MemstorageInstance
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

-- the log layer (stage R3): the size helpers, unstable, raftLog, MemoryStorage, with the
-- `proto.Clone`/`proto.Size` axioms where reached; `MemoryStorage` meets the `Storage` contract
#print axioms wp_pbEntryID
#print axioms wp_payloadSize
#print axioms wp_payloadsSize
#print axioms wp_entsSize
#print axioms wp_limitSize
#print axioms wp_extend
#print axioms unstable.wp_maybeFirstIndex
#print axioms unstable.wp_maybeLastIndex
#print axioms unstable.wp_maybeTerm
#print axioms unstable.wp_nextEntries
#print axioms unstable.wp_nextSnapshot
#print axioms unstable.wp_acceptInProgress
#print axioms unstable.wp_stableTo
#print axioms unstable.wp_shrinkEntriesArray
#print axioms unstable.wp_restore
#print axioms unstable.wp_truncateAndAppend
#print axioms unstable.wp_slice
#print axioms unstable.wp_mustCheckOutOfBounds
#print axioms raftLog.wp_lastIndex
#print axioms raftLog.wp_firstIndex
#print axioms raftLog.wp_term
#print axioms raftLog.wp_lastEntryID
#print axioms raftLog.wp_matchTerm
#print axioms raftLog.wp_commitTo
#print axioms raftLog.wp_maybeCommit
#print axioms raftLog.wp_mustCheckOutOfBounds
#print axioms raftLog.wp_slice
#print axioms raftLog.wp_entries
#print axioms raftLog.wp_snapshot
#print axioms raftLog.wp_appliedTo
#print axioms raftLog.wp_scan
#print axioms raftLog.wp_zeroTermOnOutOfBounds
#print axioms raftLog.wp_findConflictByTerm
#print axioms raftLog.wp_isUpToDate
#print axioms raftLog.wp_append
#print axioms raftLog.wp_findConflict
#print axioms raftLog.wp_maybeAppend
#print axioms raftLog.wp_restore
#print axioms raftLog.wp_stableTo
#print axioms raftLog.wp_hasNextOrInProgressSnapshot
#print axioms raftLog.wp_hasNextUnstableSnapshot
#print axioms raftLog.wp_nextUnstableEnts
#print axioms raftLog.wp_hasNextUnstableEnts
#print axioms raftLog.wp_maxAppliableIndex
#print axioms raftLog.wp_hasNextCommittedEnts
#print axioms raftLog.wp_nextCommittedEnts
#print axioms raftLog.wp_hasNextOrInProgressUnstableEnts
#print axioms raftLog.wp_acceptUnstable
#print axioms raftLog.wp_acceptApplying
#print axioms wp_newLogWithSize
#print axioms MemoryStorage.wp_lastIndex
#print axioms MemoryStorage.wp_firstIndex
#print axioms MemoryStorage.wp_LastIndex
#print axioms MemoryStorage.wp_FirstIndex
#print axioms MemoryStorage.wp_Term
#print axioms MemoryStorage.wp_Entries
#print axioms MemoryStorage.wp_SetHardState
#print axioms MemoryStorage.wp_InitialState
#print axioms MemoryStorage.wp_Snapshot
#print axioms wp_NewMemoryStorage
#print axioms MemoryStorage.wp_ApplySnapshot
#print axioms MemoryStorage.wp_Compact
#print axioms MemoryStorage.wp_CreateSnapshot
#print axioms MemoryStorage.wp_Append
#print axioms is_Storage_MemoryStorage

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
