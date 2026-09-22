Require Export New.proof.go_etcd_io.raft.election_proof.spec_raftLog__term.
Require Export New.proof.go_etcd_io.raft.election_proof.postulates_unstable__maybeTerm.
Require Export New.proof.go_etcd_io.raft.election_proof.postulates_raftLog__firstIndex.
Require Export New.proof.go_etcd_io.raft.election_proof.postulates_raftLog__lastIndex.

Module Type RAFTLOG__TERM_POSTULATES.
  Include UNSTABLE__MAYBETERM.
  Include RAFTLOG__FIRSTINDEX.
  Include RAFTLOG__LASTINDEX.
End RAFTLOG__TERM_POSTULATES.
