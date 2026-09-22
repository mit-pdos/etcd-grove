Require Export New.proof.go_etcd_io.raft.election_proof.postulates_traceBecomeLeader.

Module TraceBecomeLeaderProof (P : TRACEBECOMELEADER_POSTULATES) : TRACEBECOMELEADER.

  Lemma wp_traceBecomeLeader : wp_traceBecomeLeader_body.
  Proof.
    intros_ambient.
    intros r rs ro pri.
   wp_start as "Hm". by iApply "HΦ".
  Qed.

End TraceBecomeLeaderProof.
