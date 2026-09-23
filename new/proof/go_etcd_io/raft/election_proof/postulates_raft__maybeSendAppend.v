Require Export New.proof.go_etcd_io.raft.election_proof.spec_raft__maybeSendAppend.
Require Export New.proof.go_etcd_io.raft.election_proof.postulates_Progress__IsPaused.
Require Export New.proof.go_etcd_io.raft.election_proof.postulates_Progress__SentEntries.
Require Export New.proof.go_etcd_io.raft.election_proof.postulates_Progress__SentCommit.
Require Export New.proof.go_etcd_io.raft.election_proof.postulates_raftLog__term.
Require Export New.proof.go_etcd_io.raft.election_proof.postulates_raftLog__entries.
Require Export New.proof.go_etcd_io.raft.election_proof.postulates_raft__send.
Require Export New.proof.go_etcd_io.raft.election_proof.postulates_raft__maybeSendSnapshot.
Require Export New.proof.go_etcd_io.raft.election_proof.postulates_payloadsSize.

Module Type RAFT__MAYBESENDAPPEND_POSTULATES.
  Include PROGRESS__ISPAUSED.
  Include PROGRESS__SENTENTRIES.
  Include PROGRESS__SENTCOMMIT.
  Include INFLIGHTS__FULL.
  Include RAFTLOG__TERM.
  Include RAFTLOG__ENTRIES.
  Include SEND.
  Include RAFT__MAYBESENDSNAPSHOT.
  Include PAYLOADSSIZE.
End RAFT__MAYBESENDAPPEND_POSTULATES.
