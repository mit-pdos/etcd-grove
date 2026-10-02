Require Export New.proof.go_etcd_io.raft.election_proof.postulates_Progress__SentCommit.

Module ProgressSentCommitProof (P : PROGRESS__SENTCOMMIT_POSTULATES)
  : PROGRESS__SENTCOMMIT.

  Lemma wp_Progress__SentCommit : wp_Progress__SentCommit_body.
  Proof.
    intros_ambient.
    intros pr p commit.
    wp_start as "H". iNamed "H". iNamed "Hpr". wp_auto.
    iApply "HΦ". iExists _. iFrame "Hpv Hinfl". iPureIntro.
    progress_abs_from Habs.
  Qed.
End ProgressSentCommitProof.
