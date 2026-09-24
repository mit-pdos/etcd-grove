Require Export New.proof.go_etcd_io.raft.election_proof.spec_IsEmptyHardState.
Require Export New.proof.go_etcd_io.raft.election_proof.postulates_isHardStateEqual.

Module Type ISEMPTYHARDSTATE_POSTULATES.
  Include ISHARDSTATEEQUAL.
End ISEMPTYHARDSTATE_POSTULATES.
