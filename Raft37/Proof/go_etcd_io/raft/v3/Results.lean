/-
The raft v3.7 results ported so far into the parallel tree `Raft37/` (stage R0 of the
retarget, `notes/raft-retarget-plan.md`): `quorum`, `tracker` and `slices.Sort`, as
`Proof/go_etcd_io/raft/v3/Link.lean` links them for the verified raft. `#print axioms` of each
is its trust base (in the build log); `etc/tcb-report.py --collection
etc/tcb-collections/raft37.txt` reports on them. The tree replaces the old raft proof's when
it reaches its results (`Proof/go_etcd_io/raft/v3/Results.lean`).
-/
module

public import Raft37.Proof.go_etcd_io.raft.v3.Link

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

end EtcdGrove
end Perennial
