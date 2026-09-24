Require Export New.proof.go_etcd_io.raft.election_proof.proof_traceInitState.

Module TraceInitStatePostulates : TRACEINITSTATE_POSTULATES.
End TraceInitStatePostulates.

Module TraceInitState := TraceInitStateProof TraceInitStatePostulates.
