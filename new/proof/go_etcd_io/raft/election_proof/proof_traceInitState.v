Require Export New.proof.go_etcd_io.raft.election_proof.postulates_traceInitState.

Module TraceInitStateProof (P : TRACEINITSTATE_POSTULATES) : TRACEINITSTATE.

  Lemma wp_traceInitState : wp_traceInitState_body.
  Proof.
    intros_ambient.
    intros r.
    wp_start. by iApply "HΦ".
  Qed.

End TraceInitStateProof.
