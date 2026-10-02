Require Export New.proof.go_etcd_io.raft.election_proof.spec_raft__sendHeartbeat.
Require Export New.proof.go_etcd_io.raft.election_proof.postulates_raft__send.
Require Export New.proof.go_etcd_io.raft.election_proof.postulates_Progress__SentCommit.

Module Type RAFT__SENDHEARTBEAT_POSTULATES.
  Include SEND.
  Include PROGRESS__SENTCOMMIT.
End RAFT__SENDHEARTBEAT_POSTULATES.
