Require Export New.proof.go_etcd_io.raft.v3_proof.election.proof_big_Int__Int64.

Module BigIntInt64Postulates : BIG_INT__INT64_POSTULATES.
End BigIntInt64Postulates.

Module BigIntInt64 := BigIntInt64Proof BigIntInt64Postulates.
