Require Export New.proof.go_etcd_io.raft.v3_proof.election.proof_Inflights__Full.

Module InflightsFullPostulates : INFLIGHTS__FULL_POSTULATES.
End InflightsFullPostulates.

Module InflightsFull := InflightsFullProof InflightsFullPostulates.
