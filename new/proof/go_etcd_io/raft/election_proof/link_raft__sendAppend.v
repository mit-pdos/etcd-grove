Require Export New.proof.go_etcd_io.raft.election_proof.proof_raft__sendAppend.
Require Export New.proof.go_etcd_io.raft.election_proof.link_raft__maybeSendAppend.

Module RaftSendAppendPostulates : RAFT__SENDAPPEND_POSTULATES.
  Include RaftMaybeSendAppend.
End RaftSendAppendPostulates.

Module RaftSendAppend := RaftSendAppendProof RaftSendAppendPostulates.
