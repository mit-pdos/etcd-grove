Require Export New.proof.go_etcd_io.raft.v3_proof.election.proof_JointConfig__IDs.

Module JointConfigIDsPostulates : JOINTCONFIG__IDS_POSTULATES.
End JointConfigIDsPostulates.

Module JointConfigIDs := JointConfigIDsProof JointConfigIDsPostulates.
