Require Export New.proof.go_etcd_io.raft.election_proof.proof_raft__bcastHeartbeatWithCtx.
Require Export New.proof.go_etcd_io.raft.election_proof.link_ProgressTracker__Visit.
Require Export New.proof.go_etcd_io.raft.election_proof.link_raft__sendHeartbeat.

Module RaftBcastHeartbeatWithCtxPostulates : RAFT__BCASTHEARTBEATWITHCTX_POSTULATES.
  Include ProgressTrackerVisit.
  Include RaftSendHeartbeat.
End RaftBcastHeartbeatWithCtxPostulates.

Module RaftBcastHeartbeatWithCtx :=
  RaftBcastHeartbeatWithCtxProof RaftBcastHeartbeatWithCtxPostulates.
