Require Export New.proof.go_etcd_io.raft.election_proof.spec_raftLog__findConflict.
Require Export New.proof.go_etcd_io.raft.election_proof.postulates_pbEntryID.
Require Export New.proof.go_etcd_io.raft.election_proof.postulates_raftLog__matchTerm.
Require Export New.proof.go_etcd_io.raft.election_proof.postulates_raftLog__lastIndex.
Require Export New.proof.go_etcd_io.raft.election_proof.postulates_raftLog__term.
Require Export New.proof.go_etcd_io.raft.election_proof.postulates_raftLog__zeroTermOnOutOfBounds.

Module Type RAFTLOG__FINDCONFLICT_POSTULATES.
  Include PBENTRYID.
  Include RAFTLOG__MATCHTERM.
  Include RAFTLOG__LASTINDEX.
  Include RAFTLOG__TERM.
  Include RAFTLOG__ZEROTERMONOUTOFBOUNDS.
End RAFTLOG__FINDCONFLICT_POSTULATES.
