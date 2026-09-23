Require Export New.proof.go_etcd_io.raft.v3_proof.election.postulates_traceBecomeLeader.

Module TraceBecomeLeaderProof (P : TRACEBECOMELEADER_POSTULATES) : TRACEBECOMELEADER.

  Lemma wp_traceBecomeLeader : wp_traceBecomeLeader_body.
  Proof.
    intros_ambient.
    intros r.
    wp_start. by iApply "HΦ".
  Qed.

End TraceBecomeLeaderProof.
