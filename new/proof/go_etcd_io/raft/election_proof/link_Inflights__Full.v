Require Export New.proof.go_etcd_io.raft.election_proof.proof_Inflights__Full.

Module InflightsFullPostulates : INFLIGHTS__FULL_POSTULATES.
End InflightsFullPostulates.

Module InflightsFull := InflightsFullProof InflightsFullPostulates.
