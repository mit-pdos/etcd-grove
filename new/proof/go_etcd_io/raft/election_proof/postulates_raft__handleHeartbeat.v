Require Export New.proof.go_etcd_io.raft.election_proof.spec_raft__handleHeartbeat.
Require Export New.proof.go_etcd_io.raft.election_proof.postulates_raftLog__commitTo.
Require Export New.proof.go_etcd_io.raft.election_proof.postulates_raft__send.

Module Type RAFT__HANDLEHEARTBEAT_POSTULATES.
  Include RAFTLOG__COMMITTO.
  Include SEND.
End RAFT__HANDLEHEARTBEAT_POSTULATES.
