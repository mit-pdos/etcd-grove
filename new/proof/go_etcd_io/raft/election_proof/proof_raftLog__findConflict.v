Require Export New.proof.go_etcd_io.raft.election_proof.postulates_raftLog__findConflict.

Module RaftLogFindConflictProof (P : RAFTLOG__FINDCONFLICT_POSTULATES) : RAFTLOG__FINDCONFLICT.
Import P.

  (** The loop invariant: the prefix scanned so far matched, so the answer
      is [plog_find_conflict] of what is left ([Hfc]).  [slice.for_range]
      allocates its own counter besides the Go-level [i] (notes/gotchas.md),
      so both are in the invariant. *)
  Lemma wp_raftLog__findConflict : wp_raftLog__findConflict_body.
  Proof.
    intros_ambient.
    intros l ls es dq ents Hge.
    destruct ls as [prev sents uents lcm lap]; logstate_simpl.
    set (es_all := sents ++ uents).
    wp_start as "H". iNamed "H". wp_auto.
    iDestruct (own_slice_len with "Hes") as %[Hlen Hlen'].
    wp_alloc j as "Hj".
    iAssert (∃ (n k : w64),
      "Hj" ∷ j ↦ n ∗
      "i" ∷ i_ptr ↦ k ∗
      "Hlog" ∷ own_raftLog l (logstate.mk prev sents uents lcm lap) ∗
      "Hes" ∷ es ↦*{dq} ents ∗
      "%Hn" ∷ ⌜ (0 ≤ sint.Z n ≤ Z.of_nat (length ents))%Z ⌝ ∗
      "%Hfc" ∷ ⌜ plog_find_conflict prev es_all ents
                 = plog_find_conflict prev es_all (drop (sint.nat n) ents) ⌝)%I
      with "[Hj i Hlog Hes]" as "IH".
    { iExists (W64 0), _. iFrame. iPureIntro. split; [word|].
      replace (sint.nat (W64 0)) with 0%nat by word. by rewrite drop_0. }
    wp_auto.
    wp_for "IH".
    wp_if_destruct.
    - assert (∃ e, ents !! sint.nat n = Some e) as [e He].
      { apply lookup_lt_is_Some_2. word. }
      rewrite decide_True; last word.
      wp_apply (wp_load_slice_index (V:=raftpb.Entry.t) (t:=raftpb.Entry)
                  es (sint.Z n) ents dq e with "[$Hes]") as "Hes";
        try first [ word | iPureIntro; exact He | tc_solve | done ].
      rewrite decide_True; last word.
      iDestruct (own_slice_elem_acc (sint.Z n) e es dq ents with "Hes")
        as "[He Hesback]"; [ word | exact He | ].
      wp_auto.
      wp_apply (wp_pbEntryID with "[$He]") as "He".
      iDestruct ("Hesback" with "He") as "Hes".
      rewrite list_insert_id //.
      wp_apply (wp_raftLog__matchTerm _ (logstate.mk prev sents uents lcm lap) (ent_id e)
                  with "[$Hlog]") as "%b [Hlog %Hb]". logstate_simpl.
      assert (drop (sint.nat n) ents = e :: drop (S (sint.nat n)) ents) as Hdrop.
      { by apply drop_S. }
      destruct b.
      + (* the entry matches: keep scanning *)
        symmetry in Hb. apply bool_decide_eq_true_1 in Hb.
        wp_auto. wp_for_post.
        iFrame. iPureIntro. split; [word|].
        rewrite Hfc Hdrop /= decide_True //.
        f_equal. f_equal. word.
      + (* the first conflict: return its index *)
        symmetry in Hb. apply bool_decide_eq_false_1 in Hb.
        assert (plog_find_conflict prev es_all ents = e.(raftpb.Entry.Index')) as Hres.
        { rewrite Hfc Hdrop /= decide_False //. }
        assert (uint.Z prev.(raft.entryID.index') ≤ uint.Z e.(raftpb.Entry.Index'))%Z
          as Hgee.
        { rewrite List.Forall_forall in Hge. apply Hge.
          apply list_elem_of_In. by eapply list_elem_of_lookup_2. }
        wp_auto.
        wp_apply (wp_raftLog__lastIndex _ (logstate.mk prev sents uents lcm lap)
                    with "[$Hlog]") as "%li [Hlog %Hli]". logstate_simpl.
        destruct (decide (uint.Z e.(raftpb.Entry.Index') ≤ uint.Z li)%Z) as [Hle|Hgt].
        * (* [id.index <= lastIndex()]: the [Infof] *)
          rewrite bool_decide_eq_true_2; last done.
          wp_auto.
          wp_apply (wp_raftLog__term _ (logstate.mk prev sents uents lcm lap)
                      e.(raftpb.Entry.Index') with "[$Hlog]")
            as "%t %err (Hlog & %Herr & _)". logstate_simpl.
          assert (err = interface.nil) as -> by (apply Herr; lia).
          wp_apply (wp_raftLog__zeroTermOnOutOfBounds _ t interface.nil eq_refl).
          wp_apply wp_slice_literal.
          try (iSplitR; [ done | ]); try iIntros "% [? _]"; try wp_auto.
          iNamed "Hlog". iEval (rewrite /own_raftLog_core /=) in "Hcore". iNamed "Hcore".
          iPoseProof "Hl_logger" as "Hlgv". iEval (rewrite /is_Logger_val) in "Hlgv".
          iDestruct "Hlgv" as (lg Hlg) "#Hlgr".
          wp_auto.
          (* the logger is loaded: re-seal before [rewrite Hlg], which would
             also rewrite the [Hl_logger] the re-seal needs *)
          iAssert (own_raftLog l (logstate.mk prev sents uents lcm lap))
            with "[Hl HStorage Huents Huents_cap]" as "Hlog".
          { reseal_raftLog. }
          rewrite Hlg. try wp_auto.
          wp_apply (wp_Logger__logf with "Hlgr"); first solve_log_method.
          try wp_auto. wp_for_post.
          rewrite -Hres. iApply "HΦ". iFrame.
        * rewrite bool_decide_eq_false_2; last lia.
          wp_auto. wp_for_post.
          rewrite -Hres. iApply "HΦ". iFrame.
    - (* the whole batch matched *)
      assert (drop (sint.nat n) ents = []) as Hnil by (apply drop_ge; word).
      rewrite Hnil /= in Hfc. rewrite Hfc.
      iApply "HΦ". iFrame.
  Qed.

End RaftLogFindConflictProof.
