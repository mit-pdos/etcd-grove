Require Export New.proof.go_etcd_io.raft.election_proof.proof_Progress__MaybeUpdate.

Module ProgressMaybeUpdatePostulates : PROGRESS__MAYBEUPDATE_POSTULATES.
End ProgressMaybeUpdatePostulates.

Module ProgressMaybeUpdate :=
  ProgressMaybeUpdateProof ProgressMaybeUpdatePostulates.
