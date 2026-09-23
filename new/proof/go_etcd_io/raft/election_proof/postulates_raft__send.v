Require Export New.proof.go_etcd_io.raft.election_proof.spec_raft__send.
Require Export New.proof.go_etcd_io.raft.election_proof.postulates_traceSendMessage.

Module Type SEND_POSTULATES.
  Include TRACESENDMESSAGE.
End SEND_POSTULATES.
