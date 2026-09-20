Require Export New.proof.go_etcd_io.raft.v3_proof.election.spec_Inflights__Add.
Require Export New.proof.go_etcd_io.raft.v3_proof.election.postulates_Inflights__Full.

(** Direct callees: [Full] (the panic test) and [grow] (the buffer
    doubling).  [grow] has no collection yet -- see the [Admitted] in
    [proof_Inflights__Add.v]. *)
Module Type INFLIGHTS__ADD_POSTULATES.
  Include INFLIGHTS__FULL.
End INFLIGHTS__ADD_POSTULATES.
