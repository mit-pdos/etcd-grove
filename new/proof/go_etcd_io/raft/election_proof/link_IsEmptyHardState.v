Require Export New.proof.go_etcd_io.raft.election_proof.proof_IsEmptyHardState.
Require Export New.proof.go_etcd_io.raft.election_proof.link_isHardStateEqual.

Module IsEmptyHardStatePostulates : ISEMPTYHARDSTATE_POSTULATES.
  Include IsHardStateEqual.
End IsEmptyHardStatePostulates.

Module IsEmptyHardState := IsEmptyHardStateProof IsEmptyHardStatePostulates.
