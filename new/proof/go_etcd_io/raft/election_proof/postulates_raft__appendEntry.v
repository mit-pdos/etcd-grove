Require Export New.proof.go_etcd_io.raft.election_proof.spec_raft__appendEntry.
Require Export New.proof.go_etcd_io.raft.election_proof.postulates_raftLog__lastIndex.
Require Export New.proof.go_etcd_io.raft.election_proof.postulates_raft__increaseUncommittedSize.
Require Export New.proof.go_etcd_io.raft.election_proof.postulates_traceReplicate.
Require Export New.proof.go_etcd_io.raft.election_proof.postulates_raftLog__append.
Require Export New.proof.go_etcd_io.raft.election_proof.postulates_raft__send.

Module Type RAFT__APPENDENTRY_POSTULATES.
  Include RAFTLOG__LASTINDEX.
  Include RAFT__INCREASEUNCOMMITTEDSIZE.
  Include TRACEREPLICATE.
  Include RAFTLOG__APPEND.
  Include SEND.
End RAFT__APPENDENTRY_POSTULATES.
