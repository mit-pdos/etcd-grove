Require Export New.proof.go_etcd_io.raft.v3_proof.election.spec_Progress__SentEntries.
Require Export New.proof.go_etcd_io.raft.v3_proof.election.postulates_Inflights__Add.

Module Type PROGRESS__SENTENTRIES_POSTULATES.
  Include INFLIGHTS__ADD.
  Include INFLIGHTS__FULL.
End PROGRESS__SENTENTRIES_POSTULATES.
