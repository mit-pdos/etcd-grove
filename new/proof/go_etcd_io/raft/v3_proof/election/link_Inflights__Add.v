Require Export New.proof.go_etcd_io.raft.v3_proof.election.proof_Inflights__Add.
Require Export New.proof.go_etcd_io.raft.v3_proof.election.link_Inflights__Full.

Module InflightsAddPostulates : INFLIGHTS__ADD_POSTULATES.
  Include InflightsFull.
End InflightsAddPostulates.

Module InflightsAdd := InflightsAddProof InflightsAddPostulates.
