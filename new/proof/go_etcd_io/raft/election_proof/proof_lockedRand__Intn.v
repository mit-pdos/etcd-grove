Require Export New.proof.go_etcd_io.raft.election_proof.postulates_lockedRand__Intn.

Module LockedRandIntnProof (P : LOCKEDRAND__INTN_POSTULATES) : LOCKEDRAND__INTN.

  (** Straight-line: lock, build the bound, draw, unlock, read back.  The
      [if err != nil { panic }] is folded away by [wp_rand_Int]'s
      [#interface.nil] return, which is the point of stating that triple for
      the package's own [Reader].  The two [Convert]s ([int] to [int64] and
      back) are identities on [w64]. *)
  Lemma wp_lockedRand__Intn : wp_lockedRand__Intn_body.
  Proof.
    intros_ambient.
    intros lr n Hn.
    wp_start as "#Hlr". iEval (rewrite /is_lockedRand) in "Hlr". iNamed "Hlr". wp_auto.
    wp_apply (wp_Mutex__Lock with "[$Hmu]") as "[Hlocked _]".
    (* [rand.Reader] is loaded through [is_pkg_init rand]'s points-to *)
    iAssert (is_pkg_init rand) as "#Hrand"; first iPkgInit.
    iDestruct (is_pkg_init_access with "Hrand") as "@".
    wp_auto.
    wp_apply P.wp_big_NewInt as "%max Hmax".
    wp_apply (P.wp_rand_Int _ _ _ Hn with "[$Reader $Hmax]")
      as "%v %z (Hmax & Hv & %Hz)".
    wp_apply (wp_Mutex__Unlock with "[$Hmu $Hlocked]"); first done.
    wp_apply (P.wp_big_Int__Int64 _ _ with "[$Hv]") as "Hv".
    { pose proof (word.signed_range n). lia. }
    iApply "HΦ". iPureIntro. word.
  Qed.

End LockedRandIntnProof.
