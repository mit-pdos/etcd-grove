Require Export New.proof.go_etcd_io.raft.election_proof.proof_Progress__ResetState.
Require Export New.proof.go_etcd_io.raft.election_proof.link_Inflights__reset.

Module ProgressResetStatePostulates : PROGRESS__RESETSTATE_POSTULATES.
  Include InflightsReset.
End ProgressResetStatePostulates.

Module ProgressResetState := ProgressResetStateProof ProgressResetStatePostulates.
