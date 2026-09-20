Require Export New.proof.go_etcd_io.raft.v3_proof.election.spec_ProgressTracker__Visit.
Require Export New.proof.go_etcd_io.raft.v3_proof.election.postulates_slices_Sort.

Module Type PROGRESSTRACKER__VISIT_POSTULATES.
  (* [Visit] sorts the collected ids with [slices.Sort] before applying the
     closure; only the permutation matters (no caller's [I] sees the order). *)
  Include SLICES_SORT.
End PROGRESSTRACKER__VISIT_POSTULATES.
