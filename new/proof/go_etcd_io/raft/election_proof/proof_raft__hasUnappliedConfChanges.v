Require Export New.proof.go_etcd_io.raft.election_proof.postulates_raft__hasUnappliedConfChanges.

Module RaftHasUnappliedConfChangesProof (P : RAFT__HASUNAPPLIEDCONFCHANGES_POSTULATES) : RAFT__HASUNAPPLIEDCONFCHANGES.
Import P.

  Local Ltac read_field Hls :=
    let Hc := fresh "Hc" in
    let Ha := fresh "Ha" in
    wp_apply (wp_raft_load_raftLog with "Hphys") as "Hphys";
    iDestruct (own_raft_phys_log_same with "Hphys") as "[Hlog Hback]";
    iEval (rewrite Hls) in "Hlog";
    iDestruct (own_raftLog_struct with "Hlog") as (?) "(Hl & %Hlv & Hlb)";
    match goal with
    | H : raft.raftLog.committed' _ = _ ∧ _ |- _ => destruct H as [Hc Ha]
    end;
    simpl in Hc, Ha;
    wp_auto;
    try rewrite Hc; try rewrite Ha;
    iDestruct ("Hlb" with "Hl") as "Hlog";
    iEval (rewrite -Hls) in "Hlog";
    iDestruct ("Hback" with "Hlog") as "Hphys";
    clear Hc Ha.

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

      - No loan: the log is inside [own_raft_phys], so each read of
        [r.raftLog.f] loads the location through the struct and then takes
        the log out ([own_raft_phys_log_same]) just for the field load
        ([own_raftLog_struct]); [read_field] above.  The log's state pins
        [applied]/[committed], so every read sees the values the facts
        (unfolded once up front) are about.
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
    intros cfg r id s.
    wp_start as "Hphys".
    destruct (s.(nstate.logst)) as [prev sents uents lcm lap] eqn:Hls.
    (* the log's facts, read once: [applied]/[committed] inside the log, and
       no conf change in it.  No tracker loan: nothing here touches it. *)
    iDestruct (own_raft_phys_log_same with "Hphys") as "[Hlog Hback]".
    iEval (rewrite Hls own_raftLog_unfold) in "Hlog".
    iDestruct "Hlog" as (lv) "(Hl & %Hcm & %Hap & Hcore)".
    iEval (rewrite /own_raftLog_core /=) in "Hcore".
    iDestruct "Hcore" as (stored) "Hcore". iNamed "Hcore".
    subst lcm lap.
    iDestruct ("Hback" with "[Hl HStorage Huents Huents_cap]") as "Hphys".
    { rewrite Hls. reseal_raftLog. }
    (* each [r.raftLog.f] read: the struct gives the log's location, the
       log (taken out and put back around the one load) the field, whose
       value the log's state pins for [applied]/[committed] *)
    wp_auto.
    read_field Hls. read_field Hls.
    wp_if_destruct.
    - (* [applied >= committed]: the range is empty and the answer is [false] *)
      by iApply "HΦ".
    - (* the reads of [r.raftLog] for [lo], [hi], [pageSize] *)
      read_field Hls. read_field Hls. read_field Hls.
      wp_apply (wp_raft_load_raftLog with "Hphys") as "Hphys".
      (* [scan] is specified on [own_raftLog] *)
      iDestruct (own_raft_phys_log_same with "Hphys") as "[Hlog Hback]".
      iEval (rewrite Hls) in "Hlog".
      assert ((uint.Z prev.(raft.entryID.index') + 1
               ≤ uint.Z (word.add lv.(raft.raftLog.applied') (W64 1))
               ≤ uint.Z (word.add lv.(raft.raftLog.committed') (W64 1))
               ≤ uint.Z prev.(raft.entryID.index') + Z.of_nat (length sents)
                 + Z.of_nat (length uents) + 1)%Z) as Hrange by word.
      wp_apply (wp_raftLog__scan _ (logstate.mk prev sents uents lv.(raft.raftLog.committed') lv.(raft.raftLog.applied')) _ _ _ _ emp%I
                  (λ e, e.(raftpb.Entry.Type') = EntryNormal) Hrange HnoConfChange
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
          case_decide as Hdec; [clear Hdec | exfalso; apply Hdec; word].
          wp_apply (wp_load_slice_index (V:=raftpb.Entry.t) (t:=raftpb.Entry)
                      sl (sint.Z k) es dq e with "[$Hes]") as "Hes";
            try first [ word | iPureIntro; exact He | tc_solve | done ].
          case_decide as Hdec; [clear Hdec | exfalso; apply Hdec; word].
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
          case_decide as Hdec; [clear Hdec | exfalso; apply Hdec; word].
          wp_auto.
          rewrite HeT /EntryNormal bool_decide_eq_false_2; last w32_ne.
          wp_auto.
          iDestruct ("Hesback" with "Hel") as "Hes".
          rewrite (list_insert_id _ _ _ He).
          wp_for_post.
          iFrame. iPureIntro. word.
        + iApply "HΦ". iFrame. }
      iIntros "[Hlog _]".
      iEval (rewrite -Hls) in "Hlog".
      iDestruct ("Hback" with "Hlog") as "Hphys".
      (* [scan] returned [nil], so the [Panicf] is dead and [found] is [false] *)
      wp_auto.
      by iApply "HΦ".
  Qed.

End RaftHasUnappliedConfChangesProof.
