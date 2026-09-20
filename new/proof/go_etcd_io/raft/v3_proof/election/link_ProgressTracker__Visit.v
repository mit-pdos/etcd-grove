Require Export New.proof.go_etcd_io.raft.v3_proof.election.proof_ProgressTracker__Visit.
Require Export New.proof.go_etcd_io.raft.v3_proof.election.link_slices_Sort.

Module ProgressTrackerVisitPostulates : PROGRESSTRACKER__VISIT_POSTULATES.
  Include SlicesSort.
End ProgressTrackerVisitPostulates.

Module ProgressTrackerVisit := ProgressTrackerVisitProof ProgressTrackerVisitPostulates.
