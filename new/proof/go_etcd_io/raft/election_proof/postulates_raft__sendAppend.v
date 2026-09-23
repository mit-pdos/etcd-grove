Require Export New.proof.go_etcd_io.raft.election_proof.spec_raft__sendAppend.
Require Export New.proof.go_etcd_io.raft.election_proof.postulates_raft__maybeSendAppend.

Module Type RAFT__SENDAPPEND_POSTULATES.
  Include RAFT__MAYBESENDAPPEND.
End RAFT__SENDAPPEND_POSTULATES.
