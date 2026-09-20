Require Export New.proof.go_etcd_io.raft.v3_proof.election.proof_extend.

Module ExtendPostulates : EXTEND_POSTULATES.
End ExtendPostulates.

Module Extend := ExtendProof ExtendPostulates.
