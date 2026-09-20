Require Export New.proof.go_etcd_io.raft.v3_proof.election.spec_limitSize.
Require Export New.proof.go_etcd_io.raft.v3_proof.election.postulates_Entry__Size.

Module Type LIMITSIZE_POSTULATES.
  Include ENTRY__SIZE.
End LIMITSIZE_POSTULATES.
