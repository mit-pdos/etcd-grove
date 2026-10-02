Require Export New.proof.go_etcd_io.raft.election_proof.proof_raft__bcastHeartbeat.
Require Export New.proof.go_etcd_io.raft.election_proof.link_readOnly__heartbeatCtx.
Require Export New.proof.go_etcd_io.raft.election_proof.link_raft__bcastHeartbeatWithCtx.

Module RaftBcastHeartbeatPostulates : RAFT__BCASTHEARTBEAT_POSTULATES.
  Include ReadOnlyHeartbeatCtx.
  Include RaftBcastHeartbeatWithCtx.
End RaftBcastHeartbeatPostulates.

Module RaftBcastHeartbeat := RaftBcastHeartbeatProof RaftBcastHeartbeatPostulates.
