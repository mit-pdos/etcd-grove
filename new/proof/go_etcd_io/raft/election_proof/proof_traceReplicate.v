Require Export New.proof.go_etcd_io.raft.election_proof.postulates_traceReplicate.

Module TraceReplicateProof (P : TRACEREPLICATE_POSTULATES) : TRACEREPLICATE.

  Lemma wp_traceReplicate : wp_traceReplicate_body.
  Proof.
    intros_ambient.
    intros r es.
    wp_start. by iApply "HΦ".
  Qed.

End TraceReplicateProof.
