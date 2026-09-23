Require Export New.proof.go_etcd_io.raft.election_proof.postulates_tracker_NewInflights.

Module TrackerNewInflightsProof (P : TRACKER_NEWINFLIGHTS_POSTULATES) : TRACKER_NEWINFLIGHTS.

  Lemma wp_tracker_NewInflights : wp_tracker_NewInflights_body.
  Proof.
    intros_ambient.
    intros size maxBytes Hsz.

    wp_start as "_". wp_auto.
    (* [wp_auto] does not step a [GoAlloc] sitting in [return:] position -- the
       goal is still [WP exception_do (return: GoAlloc tracker.Inflights #{|…|})].
       Allocate explicitly.  The literal leaves [buffer' := slice.nil], so the
       buffer is the empty slice. *)
    wp_apply wp_alloc. iIntros (l) "Hl". wp_auto.
    iApply "HΦ". iExists _, []. rewrite /own_inflights /=. iFrame "Hl".
    iSplitL; [iApply own_slice_nil|].
    iSplitL; [iApply own_slice_cap_nil|].
    (* the ring-buffer invariant at a fresh [Inflights]: everything is zero
       and the buffer is empty, so only the [size] bounds have content --
       exactly the premise. *)
    iPureIntro. rewrite /inflights_ok /=. split_and!; word.
  Qed.

End TrackerNewInflightsProof.
