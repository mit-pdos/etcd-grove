/-
The raft v3.7 results (`notes/raft-retarget-plan.md`; ported into the parallel tree `Raft37/` from
stage R0 on, the raft tree since stage R6, 2026-10-16): `quorum`, `tracker` and `slices.Sort`; since stage R1
`raftpb` (the getters, `Enum`, `Ensure*`, the conf-change codec, `ConfState.Equivalent`) and the
nine protobuf-go axioms (`proto.*`, the trust boundary); since stage R2 `confchange` (with
etcd-grove's `fmt.Errorf` axiom and `raftpb.ConfChangeType.String` at the trust boundary); since
stage R3 the log layer (`unstable`, `raftLog`, `MemoryStorage`, the size helpers, over read-only
entries) and `MemoryStorage`'s instance of the `Storage` contract; since stage R4 `raft.go` over
pointer messages (every function of the layer: the struct's helpers, the `Step` dispatch and its
branches, `stepLeader`/`stepCandidate`/`stepFollower`, the constructor `newRaft`, with
`fmt.Sprintf` and `strings.Join` copied from the old tree and `DescribeConfChange` at the trust
boundary); since stage R5 the node layer over pointer messages (`rawnode.go` and `node.go`:
every `RawNode` method, `readyWithoutAccept`/`acceptReady` and their composition `Ready`,
`Advance`, the `node` API and its `run` loop, `NewRawNode`, `newNode`, `RestartNode`,
`confChangeToMsg`, and the storage-response helpers `needStorageAppendRespMsg`/
`newStorageAppendRespMsg`/`newStorageApplyRespMsg`), as `Proof/go_etcd_io/raft/v3/Link.lean`
links them for the verified raft. The old tree's results (`raft.wp_Step`, `wp_newRaft`, the
`RawNode` and `node` results) all have their counterparts here; its `Results.lean` restates no
theorem beyond their `#print axioms`. `#print axioms` of each
is its trust base (in the build log); `etc/tcb-report.py --collection
etc/tcb-collections/raft37.txt` reports on them. The tree replaces the old raft proof's when
it reaches its results (`Proof/go_etcd_io/raft/v3/Results.lean`).

Since stage R1 also the protocol model's allocation (`Protocol/ResultsDyn.lean`); the model-level
safety results (log agreement, election safety, the read index, log matching, state machine
safety, leader completeness) were removed on 2026-10-21 (branch `clean-up`): no linked result or
closed theorem used them, the client-facing guarantees being the specs' atomic updates.
-/
module

public import Proof.go_etcd_io.raft.v3.Link
-- `MemoryStorage` meets the `Storage` contract (stage R3)
public import Proof.go_etcd_io.raft.v3.MemstorageInstance
-- the protocol model's results (stage R1: the model ported)
public import Proof.go_etcd_io.raft.v3.Protocol.ResultsDyn
public import Proof.go_etcd_io.raft.v3.Protocol.Facts
public import Proof.go_etcd_io.raft.v3.StepGhostMode

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
#print axioms unstable.wp_stableSnapTo
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
#print axioms raftLog.wp_stableSnapTo
#print axioms raftLog.wp_hasNextOrInProgressSnapshot
#print axioms raftLog.wp_hasNextUnstableSnapshot
#print axioms raftLog.wp_nextUnstableSnapshot
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

-- raft.go over pointer messages (stage R4); the old tree's raft-level results first
#print axioms raft.wp_Step
#print axioms wp_newRaft
#print axioms big.wp_NewInt
#print axioms big.Int.wp_Int64
#print axioms rand.wp_Int
#print axioms wp_IsLocalMsgTarget
#print axioms Config.wp_validate
#print axioms wp_isMsgInArray
#print axioms wp_IsLocalMsg
#print axioms wp_IsResponseMsg
#print axioms wp_newReadOnly
#print axioms wp_traceInitState
#print axioms wp_traceConfChangeEvent
#print axioms wp_traceCommit
#print axioms wp_traceSendMessage
#print axioms wp_traceBecomeFollower
#print axioms wp_traceBecomeCandidate
#print axioms wp_traceBecomeLeader
#print axioms wp_traceReplicate
#print axioms wp_traceChangeConfEvent
#print axioms wp_traceReceiveMessage
#print axioms wp_traceReady
#print axioms lockedRand.wp_Intn
#print axioms raft.wp_resetRandomizedElectionTimeout
#print axioms raft.wp_abortLeaderTransfer
#print axioms raft.wp_softState
#print axioms raft.wp_hasLeader
#print axioms raft.wp_pastElectionTimeout
#print axioms raft.wp_promotable
#print axioms raft.wp_committedEntryInCurrentTerm
#print axioms raft.wp_increaseUncommittedSize
#print axioms raft.wp_reduceUncommittedSize
#print axioms raft.wp_appliedTo
#print axioms raft.wp_appliedSnap
#print axioms raft.wp_maybeCommit
#print axioms raft.wp_poll
#print axioms readOnly.wp_heartbeatCtx
#print axioms readOnly.wp_recvAck
#print axioms readOnly.wp_AckedIndex
#print axioms readOnly.wp_maybeAdvance
#print axioms wp_voteRespMsgType
#print axioms SoftState.wp_equal
#print axioms wp_needStorageApplyMsg
#print axioms wp_needStorageApplyRespMsg
#print axioms wp_stepFollower
#print axioms wp_isHardStateEqual
#print axioms wp_IsEmptyHardState
#print axioms wp_MustSync
#print axioms wp_IsEmptySnap
#print axioms wp_assertConfStatesEquivalent
#print axioms raft.wp_hardState
#print axioms raft.wp_loadState
#print axioms wp_getBasicStatus
#print axioms wp_logSliceFromMsgApp
#print axioms wp_stepCandidate
#print axioms readOnly.wp_addRequest
#print axioms raft.wp_hasUnappliedConfChanges
#print axioms raft.wp_responseToReadIndexReq
#print axioms wp_sendMsgReadIndexResponse
#print axioms wp_releasePendingReadIndexMessages
#print axioms raft.wp_tickElection
#print axioms raft.wp_tickHeartbeat
#print axioms raft.wp_send
#print axioms raft.wp_sendTimeoutNow
#print axioms raft.wp_sendHeartbeat
#print axioms raft.wp_reset
#print axioms raft.wp_becomeFollower
#print axioms raft.wp_becomeCandidate
#print axioms raft.wp_becomePreCandidate
#print axioms raft.wp_bcastHeartbeatWithCtx
#print axioms raft.wp_bcastHeartbeat
#print axioms raft.wp_sendAppend
#print axioms raft.wp_bcastAppend
#print axioms raft.wp_hup
#print axioms raft.wp_handleHeartbeat
#print axioms raft.wp_switchToConfig
#print axioms raft.wp_maybeSendSnapshot
#print axioms raft.wp_applyConfChange
#print axioms raft.wp_becomeLeader
#print axioms raft.wp_handleSnapshot
#print axioms raft.wp_maybeSendAppend
#print axioms raft.wp_campaign
#print axioms raft.wp_handleAppendEntries
#print axioms raft.wp_appendEntry
#print axioms raft.wp_restore
#print axioms fmt.wp_Sprintf
#print axioms wp_DescribeConfChange
#print axioms wp_stepLeader
#print axioms strings.wp_Join

-- the node layer, rawnode.go and node.go (stage R5)
#print axioms RawNode.wp_Ready
#print axioms RawNode.wp_Advance
#print axioms node.wp_run
#print axioms wp_RestartNode
#print axioms RawNode.wp_readyWithoutAccept
#print axioms RawNode.wp_acceptReady
#print axioms RawNode.wp_HasReady
#print axioms RawNode.wp_Propose
#print axioms RawNode.wp_ProposeConfChange
#print axioms RawNode.wp_ReadIndex
#print axioms RawNode.wp_Step
#print axioms RawNode.wp_Tick
#print axioms RawNode.wp_Campaign
#print axioms RawNode.wp_ApplyConfChange
#print axioms RawNode.wp_BasicStatus
#print axioms RawNode.wp_ForgetLeader
#print axioms RawNode.wp_TransferLeader
#print axioms RawNode.wp_ReportSnapshot
#print axioms RawNode.wp_ReportUnreachable
#print axioms wp_NewRawNode
-- the new cluster's start (stage R8b, D12): `sorryAx` until the protocol side's
-- `ownRaftGhost_alloc_boot` is proved
#print axioms RawNode.wp_Bootstrap
#print axioms wp_setupNode
#print axioms wp_StartNode
#print axioms wp_confChangeToMsg
#print axioms wp_needStorageAppendRespMsg
#print axioms wp_newStorageAppendRespMsg
#print axioms wp_newStorageApplyRespMsg
#print axioms wp_newNode
#print axioms node.wp_Propose
#print axioms node.wp_ProposeConfChange
#print axioms node.wp_ReadIndex
#print axioms node.wp_Step
#print axioms node.wp_step
#print axioms node.wp_stepWait
#print axioms node.wp_stepWithWaitOption
#print axioms node.wp_Tick
#print axioms node.wp_Ready
#print axioms node.wp_Advance
#print axioms node.wp_ApplyConfChange
#print axioms node.wp_ForgetLeader
#print axioms node.wp_Stop
#print axioms node.wp_TransferLeadership
#print axioms node.wp_ReportSnapshot
#print axioms node.wp_ReportUnreachable

-- the protocol model (stage R1)
#print axioms raft_dyn_alloc

end EtcdGrove
end Perennial
