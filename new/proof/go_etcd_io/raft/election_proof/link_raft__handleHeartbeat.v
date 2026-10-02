Require Export New.proof.go_etcd_io.raft.election_proof.proof_raft__handleHeartbeat.
Require Export New.proof.go_etcd_io.raft.election_proof.link_raftLog__commitTo.
Require Export New.proof.go_etcd_io.raft.election_proof.link_raft__send.

Module RaftHandleHeartbeatPostulates : RAFT__HANDLEHEARTBEAT_POSTULATES.
  Include RaftLogCommitTo.
  Include Send.
End RaftHandleHeartbeatPostulates.

Module RaftHandleHeartbeat :=
  RaftHandleHeartbeatProof RaftHandleHeartbeatPostulates.
