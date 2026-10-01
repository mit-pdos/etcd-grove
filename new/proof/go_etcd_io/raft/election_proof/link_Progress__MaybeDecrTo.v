Require Export New.proof.go_etcd_io.raft.election_proof.proof_Progress__MaybeDecrTo.

Module ProgressMaybeDecrToPostulates : PROGRESS__MAYBEDECRTO_POSTULATES.
End ProgressMaybeDecrToPostulates.

Module ProgressMaybeDecrTo :=
  ProgressMaybeDecrToProof ProgressMaybeDecrToPostulates.
