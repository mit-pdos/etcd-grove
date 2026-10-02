Require Export New.proof.go_etcd_io.raft.election_proof.postulates_traceCommit.

Module TraceCommitProof (P : TRACECOMMIT_POSTULATES) : TRACECOMMIT.

  Lemma wp_traceCommit : wp_traceCommit_body.
  Proof.
    intros_ambient.
    intros r.
    wp_start. by iApply "HΦ".
  Qed.

End TraceCommitProof.
