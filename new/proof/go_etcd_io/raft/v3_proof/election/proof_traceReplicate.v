Require Export New.proof.go_etcd_io.raft.v3_proof.election.postulates_traceReplicate.

Module TraceReplicateProof (P : TRACEREPLICATE_POSTULATES) : TRACEREPLICATE.

  Lemma wp_traceReplicate : wp_traceReplicate_body.
  Proof.
    intros_ambient.
    intros r es ents dq.
    wp_start as "Hes". by iApply "HΦ".
  Qed.

End TraceReplicateProof.
