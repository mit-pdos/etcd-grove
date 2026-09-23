Require Export New.proof.go_etcd_io.raft.election_proof.postulates_Progress__BecomeSnapshot.

Module ProgressBecomeSnapshotProof (P : PROGRESS__BECOMESNAPSHOT_POSTULATES)
  : PROGRESS__BECOMESNAPSHOT.
Import P.

  Lemma wp_Progress__BecomeSnapshot : wp_Progress__BecomeSnapshot_body.
  Proof.
    intros_ambient.
    intros pr pv iv snapshoti.
    wp_start as "Hpr". wp_auto.
    (* [ResetState] is specified on [own_progress] at the exact new values;
       open what it returns to step the field writes that follow *)
    assert (progress_state_ok (W64 2)) as Hst.
    { rewrite /progress_state_ok. by right; right. }
    wp_apply (wp_Progress__ResetState _ _ _ _ Hst with "[$Hpr]") as "Hpr".
    iNamed "Hpr". wp_auto.
    iApply "HΦ". iExists _, _. rewrite /own_progress. iFrame "Hpv Hinfl".
    iPureIntro. split; done.
  Qed.

End ProgressBecomeSnapshotProof.
