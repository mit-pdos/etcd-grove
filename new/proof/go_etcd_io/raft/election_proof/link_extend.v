Require Export New.proof.go_etcd_io.raft.election_proof.proof_extend.

Module ExtendPostulates : EXTEND_POSTULATES.
End ExtendPostulates.

Module Extend := ExtendProof ExtendPostulates.
