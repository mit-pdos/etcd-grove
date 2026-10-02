Require Export New.proof.go_etcd_io.raft.election_proof.postulates_raft__reset.

Module ResetProof (P : RESET_POSTULATES) : RESET.
Import P.

Section helpers.

(** What [reset]'s [Visit] has done after visiting the ids in [D]: the
    [Progress] values range over the same peers as before, and every visited
    peer's [Match] is [reset]'s. *)
Definition reset_inv (id li : w64)
    (P0 pvs : gmap w64 progress.t) (D : gset w64) : Prop :=
  dom pvs = dom P0 ∧
  ∀ k p, k ∈ D → pvs !! k = Some p →
    p.(progress.matched) = (if decide (k = id) then li else W64 0).

(** [lastIndex()]'s result, as [log_last]. *)
Lemma log_last_unsigned (ls : logstate.t) (i : w64) :
  uint.Z i = (uint.Z ls.(logstate.prev).(raft.entryID.index')
              + Z.of_nat (length ls.(logstate.sents))
              + Z.of_nat (length ls.(logstate.uents)))%Z →
  i = log_last ls.
Proof. intros H. apply word.unsigned_inj. rewrite /log_last -H. word. Qed.

Lemma reset_inv_empty id li P0 : reset_inv id li P0 P0 ∅.
Proof. split; [done|]. intros ???. set_solver. Qed.

Lemma reset_inv_step id li P0 pvs D i v :
  reset_inv id li P0 pvs D →
  is_Some (pvs !! i) →
  v.(progress.matched) = (if decide (i = id) then li else W64 0) →
  reset_inv id li P0 (<[i := v]> pvs) ({[i]} ∪ D).
Proof.
  intros [Hdom Hm] Hi Hv. split.
  - rewrite dom_insert_lookup_L //.
  - intros k p Hk Hp. destruct (decide (k = i)) as [->|Hne].
    + rewrite lookup_insert_eq in Hp. by injection Hp as <-.
    + rewrite lookup_insert_ne // in Hp. apply (Hm k); [set_solver|done].
Qed.

Lemma reset_inv_done id li P0 pvs :
  reset_inv id li P0 pvs (dom P0) →
  prvals_match pvs = reset_matched id li P0.
Proof.
  intros [Hdom Hm]. apply map_eq. intros k.
  rewrite /prvals_match /reset_matched lookup_fmap map_lookup_imap.
  destruct (pvs !! k) as [p|] eqn:Hk; destruct (P0 !! k) as [q|] eqn:HP; simpl.
  - f_equal. apply (Hm k p); [by apply elem_of_dom|done].
  - exfalso. apply not_elem_of_dom in HP. rewrite -Hdom elem_of_dom in HP. by apply HP.
  - exfalso. apply not_elem_of_dom in Hk. rewrite Hdom elem_of_dom in Hk. by apply Hk.
  - done.
Qed.

End helpers.

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
        [bcastAppend], plus (since 2026-10-01) [reset_inv]: the [Match] of
        every peer visited so far is [reset]'s.  [Visit] ends at the full
        voter set, which is the progress map's domain, so every peer's
        [Match] is known ([reset_inv_done]).  [I] also has to carry the
        frame slot of the pointer variable ([r_ptr ↦ r]).

        The Goose closure literal reduces to
        [#(func.mk <> "id" (λ: "pr", …))] by the [wp_recc] pure step, so it
        unifies with the spec's [#f] with no help. *)
  Lemma wp_raft__reset : wp_raft__reset_body.
  Proof.
    intros_ambient.
    intros cfg r id s term.
    wp_start as "Hphys".
    (* [lastIndex()] does not wrap: the closure's [pr.Match = lastIndex()]
       is then [log_last] *)
    iDestruct (own_raft_phys_log_same with "Hphys") as "[Hlog Hlb]".
    iDestruct (own_raftLog_nowrap with "Hlog") as "[%Hnw Hlog]".
    iDestruct ("Hlb" with "Hlog") as "Hphys".
    set (li0 := log_last s.(nstate.logst)).
    wp_auto.
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
    (* [Visit] owns the tracker field and lends it to the closure together
       with one [Progress].  The caller invariant is the rest of the struct
       -- the wand of [own_raft_phys_tracker_prvals] -- and [reset_inv]. *)
    iDestruct (own_raft_phys_tracker_prvals with "Hphys") as (tv1) "(Htrkf & Htrk & HI)".
    iDestruct (own_tracker_prvals_dom with "Htrk") as "[%Hpdom Htrk]".
    iDestruct (own_tracker_progress_map with "Htrk") as "(_ & %Hprdom & Htrk)".
    assert (Hdomcfg : dom s.(nstate.prvals) = cfg) by (rewrite -Hprdom -Hpdom //).
    wp_apply (wp_ProgressTracker__Visit _ _ _
                (trk.mk s2.(nstate.votes) s2.(nstate.progress) s2.(nstate.prvals)) _
                (λ D pvsx,
                 r_ptr ↦ r ∗
                 ⌜ reset_inv id li0 s.(nstate.prvals) pvsx D ⌝ ∗
                 (∀ tvx pvsx', r.[raft.raft.t, "trk"] ↦ tvx -∗
                  own_tracker cfg tvx (trk.mk s2.(nstate.votes) s2.(nstate.progress) pvsx') -∗
                  own_raft_phys cfg r id (s2 <| nstate.prvals := pvsx' |>)))%I
                with "[$Htrkf $Htrk $r $HI]")
      as "(%tvfin & %pvsfin & Htrkf & Htrk & r & %Hinv & HI)".
    { iSplitR; first (iPureIntro; apply reset_inv_empty).
      (* the [Visit] closure: re-initialise one [Progress] wholesale.  The
         [Progress] goes back into the tracker, and the tracker into the
         struct, whenever the next step needs the struct whole
         ([r.raftLog.lastIndex()], [r.id]); it is borrowed again, at the
         value [nstate.prvals] records, for the steps that need it
         ([pr.IsLearner], the store to [*pr], [pr.Match]). *)
      iModIntro. iIntros (i pr tv0 pvs0 p D).
      wp_start as "(%Hicfg & %Hpri & %Hpvi & %HmaxI & Htrkf & Hpr & Hprback &
                    r & %Hinv0 & HI)".
      cbn [trk.prs trk.votes trk.peers] in Hpri, Hpvi.
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
      iDestruct (own_tracker_lookup _ _ (trk.mk _ _ _) _ _ Hpri with "Htrk")
        as (p1 Hpv1) "[Hpr Hprback]".
      (* Keep [Hnolearner]: [own_Progress]'s [progress_abs] says
         [pv.(IsLearner') = false], and the closure has to hand it back. *)
      iDestruct "Hpr" as (pv1) "(Hpv & _ & %Habs1)".
      pose proof Habs1 as Hnolearner.
      apply progress_abs_Some in Hnolearner as (Hnolearner & _).
      wp_auto.
      wp_apply (wp_tracker_NewInflights _ _ HmaxI2) as "%ifl Hifl".
      (* the [Progress] literal has no [State] field, so [State] is the
         zero value [StateProbe]; [IsLearner] is copied across *)
      iDestruct ("Hprback" with "[Hpv Hifl]") as "Htrk".
      { iApply (own_Progress_of _ _ prstate.Probe with "Hpv Hifl"); done. }
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
        iDestruct (own_tracker_lookup _ _ (trk.mk _ _ _) _ _ Hpri with "Htrk")
          as (p2 Hpv2) "[Hpr Hprback]".
        iDestruct "Hpr" as (pv2) "(Hpv & Hinfl & %Habs2)".
        pose proof Habs2 as Hst2.
        apply progress_abs_Some in Hst2 as (Hnolearner2 & Hst2 & _).
        wp_auto.
        iDestruct ("Hprback" with "[Hpv Hinfl]") as "Htrk".
        { iApply (own_Progress_of _ _ p2.(progress.state) with "Hpv Hinfl"); done. }
        iApply "HΦ". iExists tv3, _. iFrame "Htrkf Htrk r".
        iSplitR.
        { iPureIntro. simpl. rewrite !insert_insert_eq.
          apply reset_inv_step; [done|rewrite Hpvi; by eexists|].
          rewrite decide_True //=. rewrite /li0. apply log_last_unsigned. exact Hli1. }
        iIntros (tvx pvsx) "Hf Ht". iDestruct ("HI" $! tvx pvsx with "Hf Ht") as "Hphys".
        iApply (own_raft_phys_eq with "Hphys"). reflexivity.
      + rewrite bool_decide_false //. wp_auto.
        iDestruct (own_raft_phys_tracker_prvals with "Hphys")
          as (tv3) "(Htrkf & Htrk & HI)".
        iApply "HΦ". iExists tv3, _. iFrame "Htrkf Htrk r".
        iSplitR.
        { iPureIntro. simpl. rewrite !insert_insert_eq.
          apply reset_inv_step; [done|rewrite Hpvi; by eexists|].
          rewrite decide_False //. }
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
    iSplitL.
    - iApply (own_raft_phys_eq with "Hphys").
      subst s2 s1 s0. rewrite /reset_to. destruct s. done.
    - iPureIntro. apply reset_inv_done. rewrite Hdomcfg. exact Hinv.
  Qed.

End ResetProof.
