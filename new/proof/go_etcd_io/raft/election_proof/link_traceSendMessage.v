Require Export New.proof.go_etcd_io.raft.election_proof.proof_traceSendMessage.

Module TraceSendMessagePostulates : TRACESENDMESSAGE_POSTULATES.
End TraceSendMessagePostulates.

Module TraceSendMessage := TraceSendMessageProof TraceSendMessagePostulates.
