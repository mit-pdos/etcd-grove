Require Export New.proof.go_etcd_io.raft.v3_proof.election.proof_traceBecomeCandidate.

Module TraceBecomeCandidatePostulates : TRACEBECOMECANDIDATE_POSTULATES.
End TraceBecomeCandidatePostulates.

Module TraceBecomeCandidate := TraceBecomeCandidateProof TraceBecomeCandidatePostulates.
