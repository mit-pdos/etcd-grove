Require Export New.proof.go_etcd_io.raft.v3_proof.election.spec_Inflights__Add.
Require Export New.proof.go_etcd_io.raft.v3_proof.election.postulates_Inflights__Full.
Require Export New.proof.go_etcd_io.raft.v3_proof.election.postulates_Inflights__grow.

(** Direct callees: [Full] (the panic test) and [grow] (the buffer
    doubling). *)
Module Type INFLIGHTS__ADD_POSTULATES.
  Include INFLIGHTS__FULL.
  Include INFLIGHTS__GROW.
End INFLIGHTS__ADD_POSTULATES.
