Require Export New.proof.go_etcd_io.raft.v3_proof.election.proof_traceReceiveMessage.

Module TraceReceiveMessagePostulates : TRACERECEIVEMESSAGE_POSTULATES.
End TraceReceiveMessagePostulates.

Module TraceReceiveMessage := TraceReceiveMessageProof TraceReceiveMessagePostulates.
