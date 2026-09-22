Require Export New.proof.go_etcd_io.raft.election_proof.proof_traceReceiveMessage.

Module TraceReceiveMessagePostulates : TRACERECEIVEMESSAGE_POSTULATES.
End TraceReceiveMessagePostulates.

Module TraceReceiveMessage := TraceReceiveMessageProof TraceReceiveMessagePostulates.
