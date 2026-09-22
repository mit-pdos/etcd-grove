Require Export New.proof.go_etcd_io.raft.election_proof.spec_Progress__SentEntries.
Require Export New.proof.go_etcd_io.raft.election_proof.postulates_Inflights__Add.

Module Type PROGRESS__SENTENTRIES_POSTULATES.
  Include INFLIGHTS__ADD.
  Include INFLIGHTS__FULL.
End PROGRESS__SENTENTRIES_POSTULATES.
