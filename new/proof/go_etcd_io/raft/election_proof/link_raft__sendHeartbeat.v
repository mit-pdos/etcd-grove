Require Export New.proof.go_etcd_io.raft.election_proof.proof_raft__sendHeartbeat.
Require Export New.proof.go_etcd_io.raft.election_proof.link_raft__send.
Require Export New.proof.go_etcd_io.raft.election_proof.link_Progress__SentCommit.

Module RaftSendHeartbeatPostulates : RAFT__SENDHEARTBEAT_POSTULATES.
  Include Send.
  Include ProgressSentCommit.
End RaftSendHeartbeatPostulates.

Module RaftSendHeartbeat := RaftSendHeartbeatProof RaftSendHeartbeatPostulates.
