Require Export New.proof.go_etcd_io.raft.election_proof.proof_ProgressTracker__VoterNodes.
Require Export New.proof.go_etcd_io.raft.election_proof.link_JointConfig__IDs.
Require Export New.proof.go_etcd_io.raft.election_proof.link_slices_Sort.

Module ProgressTrackerVoterNodesPostulates : PROGRESSTRACKER__VOTERNODES_POSTULATES.
  Include JointConfigIDs.  Include SlicesSort.
End ProgressTrackerVoterNodesPostulates.

Module ProgressTrackerVoterNodes := ProgressTrackerVoterNodesProof ProgressTrackerVoterNodesPostulates.
