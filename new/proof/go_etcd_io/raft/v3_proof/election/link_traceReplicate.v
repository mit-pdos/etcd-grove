Require Export New.proof.go_etcd_io.raft.v3_proof.election.proof_traceReplicate.

Module TraceReplicatePostulates : TRACEREPLICATE_POSTULATES.
End TraceReplicatePostulates.

Module TraceReplicate := TraceReplicateProof TraceReplicatePostulates.
