Require Export New.proof.go_etcd_io.raft.v3_proof.election.postulates_traceBecomeFollower.

Module TraceBecomeFollowerProof (P : TRACEBECOMEFOLLOWER_POSTULATES) : TRACEBECOMEFOLLOWER.

  Lemma wp_traceBecomeFollower : wp_traceBecomeFollower_body.
  Proof.
    intros_ambient.
    intros r.
    wp_start. by iApply "HΦ".
  Qed.

End TraceBecomeFollowerProof.
