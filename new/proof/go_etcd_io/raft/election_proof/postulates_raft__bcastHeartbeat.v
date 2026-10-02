Require Export New.proof.go_etcd_io.raft.election_proof.spec_raft__bcastHeartbeat.
Require Export New.proof.go_etcd_io.raft.election_proof.postulates_readOnly__heartbeatCtx.
Require Export New.proof.go_etcd_io.raft.election_proof.postulates_raft__bcastHeartbeatWithCtx.

Module Type RAFT__BCASTHEARTBEAT_POSTULATES.
  Include READONLY__HEARTBEATCTX.
  Include RAFT__BCASTHEARTBEATWITHCTX.
End RAFT__BCASTHEARTBEAT_POSTULATES.
