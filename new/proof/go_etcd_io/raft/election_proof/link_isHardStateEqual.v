Require Export New.proof.go_etcd_io.raft.election_proof.proof_isHardStateEqual.

Module IsHardStateEqualPostulates : ISHARDSTATEEQUAL_POSTULATES.
End IsHardStateEqualPostulates.

Module IsHardStateEqual := IsHardStateEqualProof IsHardStateEqualPostulates.
