Require Export New.proof.go_etcd_io.raft.election_proof.spec_raftLog__maybeAppend.
Require Export New.proof.go_etcd_io.raft.election_proof.postulates_raftLog__matchTerm.
Require Export New.proof.go_etcd_io.raft.election_proof.postulates_raftLog__findConflict.
Require Export New.proof.go_etcd_io.raft.election_proof.postulates_raftLog__append.
Require Export New.proof.go_etcd_io.raft.election_proof.postulates_raftLog__commitTo.

Module Type RAFTLOG__MAYBEAPPEND_POSTULATES.
  Include RAFTLOG__MATCHTERM.
  Include RAFTLOG__FINDCONFLICT.
  Include RAFTLOG__APPEND.
  Include RAFTLOG__COMMITTO.
End RAFTLOG__MAYBEAPPEND_POSTULATES.
