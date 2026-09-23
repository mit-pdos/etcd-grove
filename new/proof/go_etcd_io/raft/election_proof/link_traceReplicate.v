Require Export New.proof.go_etcd_io.raft.election_proof.proof_traceReplicate.

Module TraceReplicatePostulates : TRACEREPLICATE_POSTULATES.
End TraceReplicatePostulates.

Module TraceReplicate := TraceReplicateProof TraceReplicatePostulates.
