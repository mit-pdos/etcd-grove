Require Export New.proof.go_etcd_io.raft.v3_proof.election.proof_traceSendMessage.

Module TraceSendMessagePostulates : TRACESENDMESSAGE_POSTULATES.
End TraceSendMessagePostulates.

Module TraceSendMessage := TraceSendMessageProof TraceSendMessagePostulates.
