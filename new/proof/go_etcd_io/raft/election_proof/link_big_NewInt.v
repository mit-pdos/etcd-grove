Require Export New.proof.go_etcd_io.raft.election_proof.proof_big_NewInt.

Module BigNewIntPostulates : BIG_NEWINT_POSTULATES.
End BigNewIntPostulates.

Module BigNewInt := BigNewIntProof BigNewIntPostulates.
