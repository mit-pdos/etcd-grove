Require Export New.proof.go_etcd_io.raft.election_proof.spec_ProgressTracker__ConfState.
Require Export New.proof.go_etcd_io.raft.election_proof.postulates_MajorityConfig__Slice.

Module Type PROGRESSTRACKER__CONFSTATE_POSTULATES.
  Include MAJORITYCONFIG__SLICE.
End PROGRESSTRACKER__CONFSTATE_POSTULATES.
