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
      - [trk.ResetVotes()] runs on the tracker [own_raft_phys_tracker]
        hands out, which goes back at the empty tally.
      - [trk.Visit f] needs the tracker field, and lends it to the closure
        with one [Progress]; the closure reads [r.raftLog], [r.id] (the
        whole struct) and [r.trk.MaxInflight], [r.trk.MaxInflightBytes]
        (the tracker field), and writes [*pr].  So [I] is the wand of
        [own_raft_phys_tracker_prvals] -- the struct with a tracker-shaped
        hole, taking it back at any [Progress] values -- as in
        [bcastAppend].  The closure fills the hole whenever it needs the
        struct whole and borrows the tracker and [pr] again, at the values
        [nstate.prvals] records, when it needs them.  [I] also has to carry
        the frame slot of the pointer variable ([r_ptr ↦ r]), which is easy
        to forget.  (Until 2026-09-29 the tracker was lent out of the
        struct for the whole [Visit], [nstate.lent].)

        [Visit] is told the progress map is [s.(nstate.progress)] and hands
        the tracker back at that same map, at whatever tracker value and
        [Progress] values it returns; the postcondition's [pvs] is the
        latter.

        The Goose closure literal reduces to
        [#(func.mk <> "id" (λ: "pr", …))] by the [wp_recc] pure step, so it
        unifies with the spec's [#f] with no help. *)
  Lemma wp_raft__reset : wp_raft__reset_body.
  Proof.
    intros_ambient.
    intros cfg r id s term.
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
    (* [r.trk.ResetVotes()], on the tracker the accessor hands out; put back
       at the empty tally *)
    iDestruct (own_raft_phys_tracker with "Hphys") as (tv) "(Htrkf & Htrk & Hback)".
    wp_apply (wp_ProgressTracker__ResetVotes with "[$Htrkf $Htrk]")
      as "%votesRef [Htrkf Htrk]".
    iDestruct ("Hback" with "Htrkf Htrk") as "Hphys".
    set (s2 := s1 <| nstate.votes := ∅ |>).
    (* [Visit] owns the tracker field -- it reads [p.Progress] through its
       pointer receiver -- and lends it to the closure together with one
       [Progress].  The caller invariant [I] is the rest of the struct: the
       wand of [own_raft_phys_tracker_prvals], which takes the tracker back
       at any tracker value and any [Progress] values (see [visit_closure],
       inv_tracker.v) -- the same shape as [bcastAppend]'s. *)
    iDestruct (own_raft_phys_tracker_prvals with "Hphys") as (tv1) "(Htrkf & Htrk & HI)".
    wp_apply (wp_ProgressTracker__Visit _ _ _ s2.(nstate.votes) s2.(nstate.progress)
                s2.(nstate.prvals) _
                (r_ptr ↦ r ∗
                 (∀ tvx pvsx, r.[raft.raft.t, "trk"] ↦ tvx -∗
                  own_tracker cfg tvx s2.(nstate.votes) s2.(nstate.progress) pvsx -∗
                  own_raft_phys cfg r id (s2 <| nstate.prvals := pvsx |>)))%I
                with "[$Htrkf $Htrk $r $HI]")
      as "(%tvfin & %pvsfin & Htrkf & Htrk & r & HI)".
    { (* the [Visit] closure: re-initialise one [Progress] wholesale.  The
         [Progress] goes back into the tracker, and the tracker into the
         struct, whenever the next step needs the struct whole
         ([r.raftLog.lastIndex()], [r.id]); it is borrowed again, at the
         value [nstate.prvals] records, for the steps that need it
         ([pr.IsLearner], the store to [*pr], [pr.Match]). *)
      iModIntro. iIntros (i pr tv0 pvs0 pv iv).
      wp_start as "(%Hicfg & %Hpri & %Hpvi & %HmaxI & Htrkf & Hpr & Hprback &
                    r & HI)".
      iDestruct ("Hprback" with "Hpr") as "Htrk".
      iDestruct ("HI" with "Htrkf Htrk") as "Hphys".
      wp_auto. wp_apply (wp_raft_load_raftLog with "Hphys") as "Hphys".
      iDestruct (own_raft_phys_log_same with "Hphys") as "[Hlog Hphys]".
      wp_apply (wp_raftLog__lastIndex _ _ with "[$Hlog]")
        as "%li [Hlog %Hli0]".
      iDestruct ("Hphys" with "Hlog") as "Hphys".
      (* [r.trk.MaxInflight], [r.trk.MaxInflightBytes] through the tracker
         field, then [pr.IsLearner] and the store through [pr] *)
      iDestruct (own_raft_phys_tracker_prvals with "Hphys")
        as (tv2) "(Htrkf & Htrk & HI)".
      iDestruct (own_tracker_maxinflight with "Htrk") as "[%HmaxI2 Htrk]".
      iDestruct (own_tracker_lookup _ _ _ _ _ _ _ Hpri with "Htrk")
        as (pv1 iv1 Hpv1) "[Hpr Hprback]".
      (* Keep [Hnolearner]: [own_progress] carries
         [⌜pv.(IsLearner') = false⌝], and the closure has to hand it back.
         The [Progress] literal it writes copies [IsLearner] straight across
         from the old one, so the fact carries over unchanged -- but only if
         it is not dropped here. *)
      iDestruct "Hpr" as "(Hpv & _ & %Hnolearner & %Hst)".
      wp_auto.
      wp_apply (wp_tracker_NewInflights _ _ HmaxI2) as "%ifl Hifl".
      iDestruct "Hifl" as (ivnew bufnew) "Hifl".
      (* the [Progress] literal has no [State] field, so [State] is the
         zero value [StateProbe]; [IsLearner] is copied across *)
      iDestruct ("Hprback" with "[Hpv Hifl]") as "Htrk".
      { rewrite /own_progress. iFrame "Hpv". simpl. iFrame "Hifl".
        iPureIntro. split; [ exact Hnolearner | rewrite /progress_state_ok; by left ]. }
      iDestruct ("HI" with "Htrkf Htrk") as "Hphys".
      wp_apply (wp_raft_load_id with "Hphys") as "Hphys".
      (* Both arms end the same way: hand the field and the tracker back to
         [Visit], and the wand back to [I]. *)
      destruct (decide (i = id)) as [Hii|Hii].
      + rewrite bool_decide_true //. wp_auto. wp_apply (wp_raft_load_raftLog with "Hphys") as "Hphys".
        iDestruct (own_raft_phys_log_same with "Hphys") as "[Hlog Hphys]".
        wp_apply (wp_raftLog__lastIndex _ _ with "[$Hlog]")
          as "%li2 [Hlog %Hli1]".
        iDestruct ("Hphys" with "Hlog") as "Hphys".
        (* [pr.Match = lastIndex()]: borrow [pr] once more *)
        iDestruct (own_raft_phys_tracker_prvals with "Hphys")
          as (tv3) "(Htrkf & Htrk & HI)".
        iDestruct (own_tracker_lookup _ _ _ _ _ _ _ Hpri with "Htrk")
          as (pv2 iv2 Hpv2) "[Hpr Hprback]".
        iDestruct "Hpr" as "(Hpv & Hinfl & %Hnolearner2 & %Hst2)".
        wp_auto.
        iDestruct ("Hprback" with "[Hpv Hinfl]") as "Htrk".
        { rewrite /own_progress. iFrame "Hpv Hinfl". done. }
        iApply "HΦ". iExists tv3, _. iFrame "Htrkf Htrk r".
        iIntros (tvx pvsx) "Hf Ht". iDestruct ("HI" $! tvx pvsx with "Hf Ht") as "Hphys".
        iApply (own_raft_phys_eq with "Hphys"). reflexivity.
      + rewrite bool_decide_false //. wp_auto.
        iDestruct (own_raft_phys_tracker_prvals with "Hphys")
          as (tv3) "(Htrkf & Htrk & HI)".
        iApply "HΦ". iExists tv3, _. iFrame "Htrkf Htrk r".
        iIntros (tvx pvsx) "Hf Ht". iDestruct ("HI" $! tvx pvsx with "Hf Ht") as "Hphys".
        iApply (own_raft_phys_eq with "Hphys"). reflexivity. }
    (* [Visit] hands the field and the tracker back *)
    iDestruct ("HI" $! tvfin pvsfin with "Htrkf Htrk") as "Hphys".
    (* [pendingConfIndex := 0], [uncommittedSize := 0] *)
    try wp_auto. (wp_apply (wp_raft_store_pendingConfIndex with "Hphys") as "Hphys"; wp_apply (wp_raft_store_uncommittedSize with "Hphys") as "Hphys").
    (* [r.readOnly = newReadOnly(r.readOnly.option)] *)
    iDestruct (own_raft_phys_readOnly with "Hphys") as (ro) "(Hrof & Hro & Hback)".
    iDestruct (own_read_only_option with "Hro") as (o) "[Hopt Hroback]".
    wp_auto.
    iDestruct ("Hroback" with "Hopt") as "Hro".
    wp_apply wp_newReadOnly as "%ro' Hro'".
    iDestruct ("Hback" with "Hrof Hro'") as "Hphys".
    iApply ("HΦ" $! pvsfin).
    iApply (own_raft_phys_eq with "Hphys").
    subst s2 s1 s0. rewrite /reset_to. destruct s. done.
  Qed.

End ResetProof.
