Require Export New.proof.go_etcd_io.raft.v3_proof.election.proof_Progress__BecomeReplicate.
Require Export New.proof.go_etcd_io.raft.v3_proof.election.link_Progress__ResetState.

Module ProgressBecomeReplicatePostulates : PROGRESS__BECOMEREPLICATE_POSTULATES.
  Include ProgressResetState.
End ProgressBecomeReplicatePostulates.

Module ProgressBecomeReplicate := ProgressBecomeReplicateProof ProgressBecomeReplicatePostulates.
