Require Export New.proof.go_etcd_io.raft.election_proof.postulates_traceConfChangeEvent.

Module TraceConfChangeEventProof (P : TRACECONFCHANGEEVENT_POSTULATES) : TRACECONFCHANGEEVENT.

  Lemma wp_traceConfChangeEvent : wp_traceConfChangeEvent_body.
  Proof.
    intros_ambient.
    intros c r.
    wp_start. by iApply "HΦ".
  Qed.

End TraceConfChangeEventProof.
