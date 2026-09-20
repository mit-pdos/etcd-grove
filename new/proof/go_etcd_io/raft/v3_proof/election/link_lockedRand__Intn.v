Require Export New.proof.go_etcd_io.raft.v3_proof.election.proof_lockedRand__Intn.
Require Export New.proof.go_etcd_io.raft.v3_proof.election.link_big_NewInt.
Require Export New.proof.go_etcd_io.raft.v3_proof.election.link_rand_Int.
Require Export New.proof.go_etcd_io.raft.v3_proof.election.link_big_Int__Int64.

Module LockedRandIntnPostulates : LOCKEDRAND__INTN_POSTULATES.
  Include BigNewInt.  Include RandInt.  Include BigIntInt64.
End LockedRandIntnPostulates.

Module LockedRandIntn := LockedRandIntnProof LockedRandIntnPostulates.
