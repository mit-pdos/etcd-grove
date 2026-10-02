Require Export New.proof.go_etcd_io.raft.election_proof.spec_raft__bcastHeartbeatWithCtx.
Require Export New.proof.go_etcd_io.raft.election_proof.postulates_ProgressTracker__Visit.
Require Export New.proof.go_etcd_io.raft.election_proof.postulates_raft__sendHeartbeat.

Module Type RAFT__BCASTHEARTBEATWITHCTX_POSTULATES.
  Include PROGRESSTRACKER__VISIT.
  Include RAFT__SENDHEARTBEAT.
End RAFT__BCASTHEARTBEATWITHCTX_POSTULATES.
