Require Export New.proof.go_etcd_io.raft.election_proof.proof_rand_Int.

Module RandIntPostulates : RAND_INT_POSTULATES.
End RandIntPostulates.

Module RandInt := RandIntProof RandIntPostulates.
