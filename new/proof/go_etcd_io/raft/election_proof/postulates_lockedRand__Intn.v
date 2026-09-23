Require Export New.proof.go_etcd_io.raft.election_proof.spec_lockedRand__Intn.
Require Export New.proof.go_etcd_io.raft.election_proof.postulates_big_NewInt.
Require Export New.proof.go_etcd_io.raft.election_proof.postulates_rand_Int.
Require Export New.proof.go_etcd_io.raft.election_proof.postulates_big_Int__Int64.

Module Type LOCKEDRAND__INTN_POSTULATES.
  Include BIG_NEWINT.  Include RAND_INT.  Include BIG_INT__INT64.
End LOCKEDRAND__INTN_POSTULATES.
