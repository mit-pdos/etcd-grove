Require Export New.proof.go_etcd_io.raft.v3_proof.election.proof_Inflights__reset.

Module InflightsResetPostulates : INFLIGHTS__RESET_POSTULATES.
End InflightsResetPostulates.

Module InflightsReset := InflightsResetProof InflightsResetPostulates.
