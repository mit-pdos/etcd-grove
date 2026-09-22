Require Export New.proof.go_etcd_io.raft.election_proof.spec_limitSize.
Require Export New.proof.go_etcd_io.raft.election_proof.postulates_Entry__Size.

Module Type LIMITSIZE_POSTULATES.
  Include ENTRY__SIZE.
End LIMITSIZE_POSTULATES.
