Require Export New.proof.go_etcd_io.raft.election_proof.postulates_Progress__BecomeSnapshot.

Module ProgressBecomeSnapshotProof (P : PROGRESS__BECOMESNAPSHOT_POSTULATES)
  : PROGRESS__BECOMESNAPSHOT.
Import P.

  Lemma wp_Progress__BecomeSnapshot : wp_Progress__BecomeSnapshot_body.
  Proof.
    intros_ambient.
    intros pr p snapshoti.
    wp_start as "Hpr". wp_auto.
    (* [ResetState] is specified on [own_Progress] at the exact new record;
       open what it returns to step the field writes that follow *)
    wp_apply (wp_Progress__ResetState _ _ prstate.Snapshot with "[$Hpr]") as "Hpr".
    iNamed "Hpr". wp_auto.
    iApply "HΦ". iExists _. iFrame "Hpv Hinfl". iPureIntro.
    progress_abs_from Habs.
  Qed.
End ProgressBecomeSnapshotProof.
