Require Export New.proof.go_etcd_io.raft.v3_proof.election.proof_big_NewInt.

Module BigNewIntPostulates : BIG_NEWINT_POSTULATES.
End BigNewIntPostulates.

Module BigNewInt := BigNewIntProof BigNewIntPostulates.
