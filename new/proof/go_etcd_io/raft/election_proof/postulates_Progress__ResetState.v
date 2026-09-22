Require Export New.proof.go_etcd_io.raft.election_proof.spec_Progress__ResetState.
Require Export New.proof.go_etcd_io.raft.election_proof.postulates_Inflights__reset.

Module Type PROGRESS__RESETSTATE_POSTULATES.
  Include INFLIGHTS__RESET.
End PROGRESS__RESETSTATE_POSTULATES.
