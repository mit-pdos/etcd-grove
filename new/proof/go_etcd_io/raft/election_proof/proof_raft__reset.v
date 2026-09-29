Require Export New.proof.go_etcd_io.raft.election_proof.postulates_raft__reset.

Module ResetProof (P : RESET_POSTULATES) : RESET.
Import P.

  (** [reset term] clears the vote iff the term changes, clears [lead] and the
      vote tally, and re-initialises everything the model does not see: the
      two tick counters, the randomised election timeout, the leader-transfer
      target, every peer's [Progress], the pending-config index, the
      uncommitted size and the read-only queue.

      The structure follows the code:

      - The [if r.Term != term] is joined ([wp_if_join]) at
        [own_raft_phys] of [s0], the state with the term and vote updated;
        after the join the rest of the body is proved once.
      - [trk.Visit f] needs the tracker field, and lends it to the closure,
        which reads [r.raftLog], [r.trk.MaxInflight], [r.trk.MaxInflightBytes]
        and [r.id] -- so the tracker is *lent* out of [own_raft_phys] for the
        duration ([own_raft_phys_lend]), the field is split off with
        [own_raft_phys_trk_lent], and the caller invariant [I] carries the
        wand that takes the field back.  The closure applies that wand to
        read [r.raftLog] and [r.id], splits the field off again to read the
        two [MaxInflight] fields and to hand it back to [Visit], and
        re-establishes [I].  The log is never lent: for the closure's two
        [lastIndex()] calls it is taken out of the re-assembled
        [own_raft_phys] and put back ([own_raft_phys_log_same]).  [I] also has
        to carry the frame slot of the pointer variable ([r_ptr ↦ r]), which
        is easy to forget.

        [Visit] is told the progress map is [s.(nstate.progress)] and hands
        the tracker back at that same map, at whatever tracker value it
        returns; [own_raft_phys_unlend] then ends the loan at the empty
        tally [ResetVotes] left.

        The Goose closure literal reduces to
        [#(func.mk <> "id" (λ: "pr", …))] by the [wp_recc] pure step, so it
        unifies with the spec's [#f] with no help. *)
  Lemma wp_raft__reset : wp_raft__reset_body.
  Proof.
    intros_ambient.
    intros cfg r id s term Hlent.
    wp_start as "Hphys". wp_auto.
    set (s0 := s <| nstate.term := term |>
                 <| nstate.vote := if decide (term = s.(nstate.term))
                                   then s.(nstate.vote) else W64 0 |>).
    wp_apply (wp_raft_load_Term with "Hphys") as "Hphys".
    wp_if_join (λ v, ⌜ v = execute_val ⌝ ∗ r_ptr ↦ r ∗ term_ptr ↦ term ∗
                     own_raft_phys cfg r id s0)%I
      with "[r term Hphys]".
    (* Two arms: [r.Term != term] writes [Term] and [Vote]; otherwise
       nothing is written and the vote survives. *)
    1-2: try wp_auto.
    2: wp_apply (wp_raft_store_Term with "Hphys") as "Hphys".
    2: wp_apply (wp_raft_store_Vote with "Hphys") as "Hphys".
    1-2: iSplitR; first done.
    1-2: iFrame "r term".
    1-2: iApply (own_raft_phys_eq with "Hphys").
    { (* the term is unchanged: nothing was written *)
      rewrite /s0 decide_True //. by destruct s. }
    { rewrite /s0 decide_False //. }
    iIntros (v) "(-> & r & term & Hphys)".
    wp_auto.
    (* [lead := None], [electionElapsed := 0], [heartbeatElapsed := 0] *)
    (wp_apply (wp_raft_store_lead with "Hphys") as "Hphys"; wp_apply (wp_raft_store_electionElapsed with "Hphys") as "Hphys"; wp_apply (wp_raft_store_heartbeatElapsed with "Hphys") as "Hphys").
    wp_apply (wp_raft__resetRandomizedElectionTimeout with "[$Hphys]") as "Hphys".
    wp_apply (wp_raft__abortLeaderTransfer with "[$Hphys]") as "Hphys".
    set (s1 := s0 <| nstate.lead := W64 0 |>).
    iDestruct (own_raft_phys_lend _ _ _ s1 Hlent with "Hphys")
      as (tv) "(Htrk & Hphys)".
    set (sL := s1 <| nstate.lent := Some tv |>).
    iDestruct (own_raft_phys_trk_lent with "Hphys")
      as "[Htrkf Hback]".
    wp_apply (wp_ProgressTracker__ResetVotes with "[$Htrkf $Htrk]")
      as "%votesRef [Htrkf Htrk]".
    (* [Visit] owns the tracker field -- it reads [p.Progress] through its
       pointer receiver -- and lends it to the closure, so [I] carries the
       wand taking it back.  The wand stays **quantified** over the field
       value: [Visit] may hand the field back at a different tracker value
       (see [visit_closure], inv_tracker.v). *)
    wp_apply (wp_ProgressTracker__Visit _ _ _ _ s.(nstate.progress) _
                (r_ptr ↦ r ∗
                 (∀ tvx, r.[raft.raft.t, "trk"] ↦ tvx -∗
                  own_raft_phys cfg r id (sL <| nstate.lent := Some tvx |>)))%I
                with "[$Htrkf $Htrk $r $Hback]")
      as "(%tvfin & Htrkf & Htrk & r & Hback)".
    { (* the [Visit] closure: re-initialise one [Progress] wholesale *)
      iModIntro. iIntros (i pr tv0).
      wp_start as "(%Hicfg & %Hpri & %HmaxI & Htrkf & Hpr & Hprback &
                    r & Hback)".
      (* Keep [Hnolearner]: [own_progress] carries
         [⌜pv.(IsLearner') = false⌝], and the closure has to hand it back.
         The [Progress] literal it writes copies [IsLearner] straight across
         from the old one, so the fact carries over unchanged -- but only if
         it is not dropped here. *)
      iDestruct "Hpr" as (pv ivold) "(Hpv & Hinfl & %Hnolearner & %Hst)".
      iDestruct ("Hback" $! tv0 with "Htrkf") as "Hphys".
      wp_auto. wp_apply (wp_raft_load_raftLog with "Hphys") as "Hphys".
      iDestruct (own_raft_phys_log_same with "Hphys") as "[Hlog Hphys]".
      wp_apply (wp_raftLog__lastIndex _ _ with "[$Hlog]")
        as "%li [Hlog %Hli0]".
      iDestruct ("Hphys" with "Hlog") as "Hphys".
      (* [r.trk.MaxInflight], [r.trk.MaxInflightBytes]: fields of the
         tracker, read through the tracker field *)
      iDestruct (own_raft_phys_trk_lent with "Hphys")
        as "[Htrkf Hback]".
      wp_auto.
      wp_apply (wp_tracker_NewInflights _ _ HmaxI) as "%ifl Hifl".
      iDestruct "Hifl" as (ivnew bufnew) "Hifl".
      iDestruct ("Hback" $! tv0 with "Htrkf") as "Hphys".
      wp_apply (wp_raft_load_id with "Hphys") as "Hphys".
      (* Both arms end the same way: hand the field back to [Visit], the
         [Progress] back to the tracker, and the wand back to [I]. *)
      destruct (decide (i = id)) as [Hii|Hii].
      + rewrite bool_decide_true //. wp_auto. wp_apply (wp_raft_load_raftLog with "Hphys") as "Hphys".
        iDestruct (own_raft_phys_log_same with "Hphys") as "[Hlog Hphys]".
        wp_apply (wp_raftLog__lastIndex _ _ with "[$Hlog]")
          as "%li2 [Hlog %Hli1]".
        iDestruct ("Hphys" with "Hlog") as "Hphys".
        iDestruct (own_raft_phys_trk_lent with "Hphys")
          as "[Htrkf Hback]".
        iApply "HΦ". iExists tv0. iFrame "Htrkf r".
        iSplitL "Hpv Hifl Hprback".
        { iApply "Hprback". iExists _, ivnew. rewrite /own_progress. iFrame "Hpv". simpl. iFrame "Hifl".
          (* the [Progress] literal has no [State] field, so [State] is the
             zero value [StateProbe]; [IsLearner] is copied across *)
          iPureIntro. split; [ exact Hnolearner | rewrite /progress_state_ok; by left ]. }
        iIntros (tvx) "Hf". iDestruct ("Hback" $! tvx with "Hf") as "Hphys".
        iApply (own_raft_phys_eq with "Hphys"). reflexivity.
      + rewrite bool_decide_false //. wp_auto.
        iDestruct (own_raft_phys_trk_lent with "Hphys")
          as "[Htrkf Hback]".
        iApply "HΦ". iExists tv0. iFrame "Htrkf r".
        iSplitL "Hpv Hifl Hprback".
        { iApply "Hprback". iExists _, ivnew. rewrite /own_progress. iFrame "Hpv". simpl. iFrame "Hifl".
          iPureIntro. split; [ exact Hnolearner | rewrite /progress_state_ok; by left ]. }
        iIntros (tvx) "Hf". iDestruct ("Hback" $! tvx with "Hf") as "Hphys".
        iApply (own_raft_phys_eq with "Hphys"). reflexivity. }
    (* [Visit] hands the field back; end the loan at [ResetVotes]'s tally *)
    iDestruct ("Hback" $! tvfin with "Htrkf") as "Hphys".
    iDestruct (own_raft_phys_unlend _ _ _ sL tvfin ∅
                 s.(nstate.progress)
                 with "Hphys Htrk") as "Hphys".
    (* [pendingConfIndex := 0], [uncommittedSize := 0] *)
    try wp_auto. (wp_apply (wp_raft_store_pendingConfIndex with "Hphys") as "Hphys"; wp_apply (wp_raft_store_uncommittedSize with "Hphys") as "Hphys").
    (* [r.readOnly = newReadOnly(r.readOnly.option)] *)
    iDestruct (own_raft_phys_readOnly with "Hphys") as (ro) "(Hrof & Hro & Hback)".
    iDestruct (own_read_only_option with "Hro") as (o) "[Hopt Hroback]".
    wp_auto.
    iDestruct ("Hroback" with "Hopt") as "Hro".
    wp_apply wp_newReadOnly as "%ro' Hro'".
    iDestruct ("Hback" with "Hrof Hro'") as "Hphys".
    iApply "HΦ".
    iApply (own_raft_phys_eq with "Hphys").
    pose proof (nstate_idle_lent _ Hlent) as Hlent0.
    subst sL s1 s0. rewrite /reset_to. destruct s; simpl in Hlent0; subst. done.
  Qed.

End ResetProof.
