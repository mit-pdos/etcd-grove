Require Export New.proof.go_etcd_io.raft.election_proof.spec_ProgressTracker__VoterNodes.
Require Export New.proof.go_etcd_io.raft.election_proof.postulates_JointConfig__IDs.
Require Export New.proof.go_etcd_io.raft.election_proof.postulates_slices_Sort.

Module Type PROGRESSTRACKER__VOTERNODES_POSTULATES.
  Include JOINTCONFIG__IDS.  Include SLICES_SORT.
End PROGRESSTRACKER__VOTERNODES_POSTULATES.
