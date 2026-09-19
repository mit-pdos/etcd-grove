Require Export New.proof.go_etcd_io.raft.v3_proof.election.proof_raft__bcastAppend.

Module RaftBcastAppendPostulates : RAFT__BCASTAPPEND_POSTULATES.
End RaftBcastAppendPostulates.

Module RaftBcastAppend := RaftBcastAppendProof RaftBcastAppendPostulates.
