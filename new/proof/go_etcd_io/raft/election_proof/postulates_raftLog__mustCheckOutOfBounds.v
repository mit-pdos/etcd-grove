Require Export New.proof.go_etcd_io.raft.election_proof.spec_raftLog__mustCheckOutOfBounds.
Require Export New.proof.go_etcd_io.raft.election_proof.postulates_raftLog__firstIndex.
Require Export New.proof.go_etcd_io.raft.election_proof.postulates_raftLog__lastIndex.

Module Type RAFTLOG__MUSTCHECKOUTOFBOUNDS_POSTULATES.
  Include RAFTLOG__FIRSTINDEX.
  Include RAFTLOG__LASTINDEX.
End RAFTLOG__MUSTCHECKOUTOFBOUNDS_POSTULATES.
