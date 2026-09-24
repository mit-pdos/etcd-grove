Require Export New.proof.go_etcd_io.raft.election_proof.postulates_raft__hasUnappliedConfChanges.

Module RaftHasUnappliedConfChangesProof (P : RAFT__HASUNAPPLIEDCONFCHANGES_POSTULATES) : RAFT__HASUNAPPLIEDCONFCHANGES.
Import P.

  (** [hasUnappliedConfChanges] is

        if r.raftLog.applied >= r.raftLog.committed { return false }
        found := false
        lo, hi := r.raftLog.applied+1, r.raftLog.committed+1
        pageSize := r.raftLog.maxApplyingEntsSize
        if err := r.raftLog.scan(lo, hi, pageSize, func(ents []pb.Entry) error {
            for i := range ents {
                if ents[i].Type == pb.EntryConfChange ||
                   ents[i].Type == pb.EntryConfChangeV2 {
                    found = true
                    return errBreak
                }
            }
            return nil
        }); err != nil && err != errBreak {
            r.logger.Panicf(...)
        }
        return found

      Both arms of the first [if] are live — nothing in scope decides
      [applied >= committed] — so the [scan] is genuinely reached and the
      proof really has to walk the entries.

      - The early return needs only that [own_raftLog] can be closed again:
        the two field reads go through [own_raftLog]'s [Hl].
      - For the [scan], [Happlied]/[Hcommitted]/[Hnowrap] put
        [[applied+1, committed+1)] inside the log without wrapping, which is
        exactly [wp_raftLog__scan]'s range premise, and [HnoConfChange]
        is its [Forall P (sents ++ uents)] premise at
        [P := λ e, e.(Type') = EntryNormal].
      - The invariant [I] handed to [scan] is [emp].  The closure's only
        write is [found = true], which is on the dead branch, so it needs no
        ownership of the enclosing frame — which is what lets the closure
        obligation be proved under the [□] that [scan_closure] sits behind.
        (Had the write been live, [found_ptr ↦ _] would have had to go into
        [I], as [reset] does with [r_ptr ↦ r] for [Visit].)
      - [errBreak] is therefore never returned, [scan] returns [nil], the
        [Panicf] is dead and [found] is still [false].

      Inside the closure, [slice.for_range] reduces to a [for:] over an
      index [j] with *two* reads of the same element per iteration: the
      range construct's own [![Entry] (IndexRef …)] (the ignored [$value]),
      and the body's [ents[i].Type], twice.  Each [IndexRef] only becomes a
      [decide] on the bounds when [wp_auto] steps it, so a [rewrite
      decide_True] is needed *after* each [wp_auto] that exposes one, not
      once up front.  The whole-element read uses [wp_load_slice_index]; the
      field reads cannot (the load is at the field, not the element), so the
      element's points-to is taken out with [own_slice_elem_acc] and put
      back with [list_insert_id]. *)
  Lemma wp_raft__hasUnappliedConfChanges : wp_raft__hasUnappliedConfChanges_body.
  Proof.
    intros_ambient.
    intros cfg r id s Hlent.
    (* the state the loan ends at is [s] again *)
    assert (s <| nstate.lent := None |> <| nstate.votes := s.(nstate.votes) |>
              <| nstate.progress := s.(nstate.progress) |> = s) as Hs.
    { destruct s; cbn in Hlent; by subst. }
    wp_start as "Hphys".
    (* the log is borrowed for the whole call, with the tracker coming along
       unused: [r.raftLog] is re-read for every field access, and those loads
       need the struct *)
    iDestruct (own_raft_phys_lend _ _ _ _ Hlent with "Hphys")
      as (tv ls Hls) "(Htrk & Hlog & Hphys)".
    destruct ls as [prev sents uents lcm lap lpg]; logstate_simpl; subst lpg.
    iNamed "Hlog".
    iEval (rewrite /own_raftLog_core /=) in "Hcore". iNamed "Hcore".
    wp_auto.
    (* the two reads of [r.raftLog] in the first [if] *)
    do 2 (wp_raft_field; try wp_auto).
    wp_if_destruct.
    - (* [applied >= committed]: the range is empty and the answer is [false] *)
      iAssert (own_raftLog s.(nstate.log) (logstate.mk prev sents uents lcm lap None))
        with "[Hl HStorage Huents Huents_cap]" as "Hlog".
      { iApply own_raftLog_unfold. iExists lv. rewrite /own_raftLog_core.
        iFrame "∗#%". }
      iDestruct (own_raft_phys_unlend with "Hphys Htrk Hlog") as "Hphys"; first done.
      iApply "HΦ". iApply (own_raft_phys_eq with "Hphys"). exact Hs.
    - (* the reads of [r.raftLog] for [lo], [hi], [pageSize] and [scan]'s
         receiver *)
      repeat (wp_raft_field; try wp_auto).
      (* re-seal the log: [scan] is specified on [own_raftLog] *)
      iAssert (own_raftLog s.(nstate.log) (logstate.mk prev sents uents lcm lap None))
        with "[Hl HStorage Huents Huents_cap]" as "Hlog".
      { iApply own_raftLog_unfold. iExists lv. rewrite /own_raftLog_core.
        iFrame "∗#%". }
      assert ((uint.Z prev.(raft.entryID.index') + 1
               ≤ uint.Z (word.add lv.(raft.raftLog.applied') (W64 1))
               ≤ uint.Z (word.add lv.(raft.raftLog.committed') (W64 1))
               ≤ uint.Z prev.(raft.entryID.index') + Z.of_nat (length sents)
                 + Z.of_nat (length uents) + 1)%Z) as Hrange by word.
      wp_apply (wp_raftLog__scan _ (logstate.mk prev sents uents lcm lap None) _ _ _ _ emp%I
                  (λ e, e.(raftpb.Entry.Type') = EntryNormal) eq_refl Hrange HnoConfChange
                  with "[$Hlog]").
      { (* the callback, at [I := emp] *)
        iSplitR; first done.
        iModIntro. iIntros (sl es dq).
        wp_start as "(Hes & %HPes & _)".
        (* [wp_auto] stops at the [for_range]'s own counter, which clashes
           with the body'sl [i]; allocate it by hand *)
        wp_auto. wp_alloc j_ptr as "j". wp_auto.
        iDestruct (slice_len_Z with "Hes") as %Hslen.
        iAssert (∃ (k m : w64),
           "j" ∷ j_ptr ↦ k ∗ "i" ∷ i_ptr ↦ m ∗ "Hes" ∷ sl ↦*{dq} es ∗
           "%Hk" ∷ ⌜ (0 ≤ sint.Z k ≤ Z.of_nat (length es))%Z ⌝)%I
          with "[j i Hes]" as "IH".
        { iFrame. iPureIntro. word. }
        wp_for "IH".
        wp_if_destruct.
        + assert (∃ e, es !! Z.to_nat (sint.Z k) = Some e) as [e He]
            by (apply lookup_lt_is_Some_2; word).
          (* the range construct'sl own read of [ents[j]] *)
          rewrite decide_True; last word.
          wp_apply (wp_load_slice_index (V:=raftpb.Entry.t) (t:=raftpb.Entry)
                      sl (sint.Z k) es dq e with "[$Hes]") as "Hes";
            try first [ word | iPureIntro; exact He | tc_solve | done ].
          rewrite decide_True; last word.
          assert (e.(raftpb.Entry.Type') = EntryNormal) as HeT.
          { rewrite List.Forall_forall in HPes. apply HPes, list_elem_of_In.
            by eapply list_elem_of_lookup_2. }
          (* the two [ents[i].Type] reads load a *field*, so lend the
             element out rather than using [wp_load_slice_index] *)
          iDestruct (own_slice_elem_acc (V:=raftpb.Entry.t) (sint.Z k) e sl dq es
                       with "Hes") as "[Hel Hesback]"; [word | exact He | ].
          wp_auto.
          rewrite HeT /EntryNormal bool_decide_eq_false_2; last w32_ne.
          wp_auto.
          rewrite decide_True; last word.
          wp_auto.
          rewrite HeT /EntryNormal bool_decide_eq_false_2; last w32_ne.
          wp_auto.
          iDestruct ("Hesback" with "Hel") as "Hes".
          rewrite (list_insert_id _ _ _ He).
          wp_for_post.
          iFrame. iPureIntro. word.
        + iApply "HΦ". iFrame. }
      iIntros "[Hlog _]".
      (* [scan] returned [nil], so the [Panicf] is dead and [found] is [false] *)
      wp_auto.
      iDestruct (own_raft_phys_unlend with "Hphys Htrk Hlog") as "Hphys"; first done.
      iApply "HΦ". iApply (own_raft_phys_eq with "Hphys"). exact Hs.
  Qed.

End RaftHasUnappliedConfChangesProof.
