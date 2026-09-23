Require Export New.proof.go_etcd_io.raft.election_proof.spec_raftLog__slice.
Require Export New.proof.go_etcd_io.raft.election_proof.postulates_raftLog__mustCheckOutOfBounds.
Require Export New.proof.go_etcd_io.raft.election_proof.postulates_unstable__slice.
Require Export New.proof.go_etcd_io.raft.election_proof.postulates_limitSize.
Require Export New.proof.go_etcd_io.raft.election_proof.postulates_entsSize.
Require Export New.proof.go_etcd_io.raft.election_proof.postulates_extend.

Module Type RAFTLOG__SLICE_POSTULATES.
  Include RAFTLOG__MUSTCHECKOUTOFBOUNDS.
  Include UNSTABLE__SLICE.
  Include LIMITSIZE.
  Include ENTSSIZE.
  Include EXTEND.
End RAFTLOG__SLICE_POSTULATES.
