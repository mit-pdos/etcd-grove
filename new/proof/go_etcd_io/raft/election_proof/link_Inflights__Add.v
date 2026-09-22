Require Export New.proof.go_etcd_io.raft.election_proof.proof_Inflights__Add.
Require Export New.proof.go_etcd_io.raft.election_proof.link_Inflights__Full.
Require Export New.proof.go_etcd_io.raft.election_proof.link_Inflights__grow.

Module InflightsAddPostulates : INFLIGHTS__ADD_POSTULATES.
  Include InflightsFull.
  Include InflightsGrow.
End InflightsAddPostulates.

Module InflightsAdd := InflightsAddProof InflightsAddPostulates.
