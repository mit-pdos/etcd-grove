Require Export New.proof.go_etcd_io.raft.v3_proof.election.spec_raft__becomeLeader.
Require Export New.proof.go_etcd_io.raft.v3_proof.election.postulates_raft__reset.
Require Export New.proof.go_etcd_io.raft.v3_proof.election.postulates_traceBecomeLeader.
Require Export New.proof.go_etcd_io.raft.v3_proof.election.postulates_raftLog__lastIndex.
Require Export New.proof.go_etcd_io.raft.v3_proof.election.postulates_raft__appendEntry.
Require Export New.proof.go_etcd_io.raft.v3_proof.election.postulates_Progress__BecomeReplicate.

Module Type BECOMELEADER_POSTULATES.
  Include RESET.  Include TRACEBECOMELEADER.
  Include RAFTLOG__LASTINDEX.
  Include RAFT__APPENDENTRY.
  Include PROGRESS__BECOMEREPLICATE.
End BECOMELEADER_POSTULATES.
