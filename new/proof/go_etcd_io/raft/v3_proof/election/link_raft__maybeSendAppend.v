Require Export New.proof.go_etcd_io.raft.v3_proof.election.proof_raft__maybeSendAppend.
Require Export New.proof.go_etcd_io.raft.v3_proof.election.link_Progress__IsPaused.
Require Export New.proof.go_etcd_io.raft.v3_proof.election.link_Progress__SentEntries.
Require Export New.proof.go_etcd_io.raft.v3_proof.election.link_Progress__SentCommit.
Require Export New.proof.go_etcd_io.raft.v3_proof.election.link_raftLog__term.
Require Export New.proof.go_etcd_io.raft.v3_proof.election.link_raftLog__entries.
Require Export New.proof.go_etcd_io.raft.v3_proof.election.link_raft__send.
Require Export New.proof.go_etcd_io.raft.v3_proof.election.link_raft__maybeSendSnapshot.
Require Export New.proof.go_etcd_io.raft.v3_proof.election.link_payloadsSize.

Module RaftMaybeSendAppendPostulates : RAFT__MAYBESENDAPPEND_POSTULATES.
  Include ProgressIsPaused.
  Include ProgressSentEntries.
  Include ProgressSentCommit.
  Include InflightsFull.
  Include RaftLogTerm.
  Include RaftLogEntries.
  Include Send.
  Include RaftMaybeSendSnapshot.
  Include PayloadsSize.
End RaftMaybeSendAppendPostulates.

Module RaftMaybeSendAppend :=
  RaftMaybeSendAppendProof RaftMaybeSendAppendPostulates.
