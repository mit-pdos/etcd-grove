Require Export New.proof.go_etcd_io.raft.election_proof.spec_raftLog__maybeCommit.
Require Export New.proof.go_etcd_io.raft.election_proof.postulates_raftLog__matchTerm.
Require Export New.proof.go_etcd_io.raft.election_proof.postulates_raftLog__commitTo.

Module Type RAFTLOG__MAYBECOMMIT_POSTULATES.
  Include RAFTLOG__MATCHTERM.
  Include RAFTLOG__COMMITTO.
End RAFTLOG__MAYBECOMMIT_POSTULATES.
