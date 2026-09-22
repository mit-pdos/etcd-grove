Require Export New.proof.go_etcd_io.raft.election_proof.proof_Progress__BecomeSnapshot.
Require Export New.proof.go_etcd_io.raft.election_proof.link_Progress__ResetState.

Module ProgressBecomeSnapshotPostulates : PROGRESS__BECOMESNAPSHOT_POSTULATES.
  Include ProgressResetState.
End ProgressBecomeSnapshotPostulates.

Module ProgressBecomeSnapshot :=
  ProgressBecomeSnapshotProof ProgressBecomeSnapshotPostulates.
