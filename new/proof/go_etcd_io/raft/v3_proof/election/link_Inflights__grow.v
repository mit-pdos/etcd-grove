Require Export New.proof.go_etcd_io.raft.v3_proof.election.proof_Inflights__grow.

Module InflightsGrowPostulates : INFLIGHTS__GROW_POSTULATES.
End InflightsGrowPostulates.

Module InflightsGrow := InflightsGrowProof InflightsGrowPostulates.
