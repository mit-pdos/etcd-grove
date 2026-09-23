Require Export New.proof.go_etcd_io.raft.election_proof.spec_raft__becomeLeader.
Require Export New.proof.go_etcd_io.raft.election_proof.postulates_raft__reset.
Require Export New.proof.go_etcd_io.raft.election_proof.postulates_traceBecomeLeader.
Require Export New.proof.go_etcd_io.raft.election_proof.postulates_raftLog__lastIndex.
Require Export New.proof.go_etcd_io.raft.election_proof.postulates_raft__appendEntry.
Require Export New.proof.go_etcd_io.raft.election_proof.postulates_Progress__BecomeReplicate.

Module Type BECOMELEADER_POSTULATES.
  Include RESET.  Include TRACEBECOMELEADER.
  Include RAFTLOG__LASTINDEX.
  Include RAFT__APPENDENTRY.
  Include PROGRESS__BECOMEREPLICATE.
End BECOMELEADER_POSTULATES.
