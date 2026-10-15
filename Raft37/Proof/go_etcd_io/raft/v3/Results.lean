/-
The raft v3.7 results ported so far into the parallel tree `Raft37/` (stage R0 of the
retarget, `notes/raft-retarget-plan.md`): `quorum`, `tracker` and `slices.Sort`, as
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
