Require Export New.proof.go_etcd_io.raft.election_proof.proof_traceCommit.

Module TraceCommitPostulates : TRACECOMMIT_POSTULATES.
End TraceCommitPostulates.

Module TraceCommit := TraceCommitProof TraceCommitPostulates.
