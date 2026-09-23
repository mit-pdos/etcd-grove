Require Export New.proof.go_etcd_io.raft.election_proof.proof_Inflights__grow.

Module InflightsGrowPostulates : INFLIGHTS__GROW_POSTULATES.
End InflightsGrowPostulates.

Module InflightsGrow := InflightsGrowProof InflightsGrowPostulates.
