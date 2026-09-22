Require Export New.proof.go_etcd_io.raft.v3_proof.election.postulates_raft__reset.

Module ResetProof (P : RESET_POSTULATES) : RESET.
Import P.

Section helper.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : raft.Assumptions}.

(** Split the [trk] field out of the whole-struct points-to, keeping a wand
    that accepts *any* new tracker value.

    The generated [AccessStrict] instance ([raft_access_store_trk]) is not
    usable here.  Its [A'] fixes the new field value, and the value
    [trk.ResetVotes()] installs is only introduced by that call's
    postcondition -- i.e. *after* the evar standing for [A'] was created, so
    it is outside that evar's scope and Iris refuses with

      iSpecialize: cannot instantiate (… ↦ ?t -∗ …) with (… ↦ tv <|Votes' := votesRef|>)

    Quantifying inside the wand avoids the evar entirely.  Proving it needs
    the whole-struct points-to unsealed into its field points-tos; contrary to
    a note in notes/gotchas.md, [iNamed] *does* fire on the result once the
    trailing [⌜l ≠ null⌝] has been peeled off. *)
Local Lemma raft_split_trk (l : loc) (rv : raft.raft.t) :
  l ↦ rv -∗
  l.[raft.raft.t, "trk"] ↦ rv.(raft.raft.trk') ∗
  (∀ tv, l.[raft.raft.t, "trk"] ↦ tv -∗ l ↦ (rv <| raft.raft.trk' := tv |>)).
Proof.
  iIntros "Hr".
  iEval (rewrite typed_pointsto_unseal /typed_pointsto_wrap /=) in "Hr".
  iDestruct "Hr" as "[Hf %Hnn]". iNamed "Hf".
  iFrame "trk".
  iIntros (tv) "Htv".
  iEval (rewrite typed_pointsto_unseal /typed_pointsto_wrap /=).
  iFrame "∗%".
Qed.

(** The same split, but with the continuation at the *same* field value, so
    that it concludes [l ↦ rv] on the nose rather than
    [l ↦ (rv <| trk' := tv |>)].

    [reset]'s [Visit] closure needs exactly this: it is handed the field by
    [Visit], applies the wand carried in [I] to read [r.raftLog] and [r.id],
    and must then hand the field back and restore [I] -- whose wand is stated
    at the *unchanged* struct value.  Deriving it from [raft_split_trk] would
    need a setter-identity rewrite ([rv <| trk' := rv.(trk') |> = rv]), which
    is not an [eq] anything in scope proves; unsealing again is three lines. *)
Local Lemma raft_split_trk_id (l : loc) (rv : raft.raft.t) :
  l ↦ rv -∗
  l.[raft.raft.t, "trk"] ↦ rv.(raft.raft.trk') ∗
  (l.[raft.raft.t, "trk"] ↦ rv.(raft.raft.trk') -∗ l ↦ rv).
Proof.
  iIntros "Hr".
  iEval (rewrite typed_pointsto_unseal /typed_pointsto_wrap /=) in "Hr".
  iDestruct "Hr" as "[Hf %Hnn]". iNamed "Hf".
  iFrame "trk".
  iIntros "Htv".
  iEval (rewrite typed_pointsto_unseal /typed_pointsto_wrap /=).
  iFrame "∗%".
Qed.

End helper.

  (** [reset term] clears the vote iff the term changes, clears [lead] and the
      vote tally, and re-initialises everything the model does not see: the
      two tick counters, the randomised election timeout, the leader-transfer
      target, every peer's [Progress], the pending-config index, the
      uncommitted size and the read-only queue.

      The structure follows the code:

      - The [if r.Term != term] is joined ([wp_if_join]) at
        [own_raft_phys] of [s0], the state with the term and vote updated.
        Both arms re-seal with [own_raft_phys_intro]; after the join the
        rest of the body is proved once.
      - [lead := None] and the two tick counters are written, and the struct
        is re-sealed at [s1] for [resetRandomizedElectionTimeout] and
        [abortLeaderTransfer], whose specs are on [own_raft_phys].
      - [trk.Visit f] is given the caller invariant [I], and the closure
        reads [r.raftLog], [r.trk.MaxInflight], [r.trk.MaxInflightBytes] and
        [r.id], all through the pointer variable the enclosing frame holds --
        so [I] also has to carry that frame slot ([r_ptr ↦ r]), which is easy
        to forget.

        [I] carries the [raft_split_trk] *continuation wand* rather than
        [r ↦ rv] itself.  It has to: [Visit] owns [trk ↦ tv] (it reads
        [p.Progress] every iteration) and lends it to the closure, which
        needs it for [r.trk.MaxInflight] -- so the field cannot also be
        inside an [r ↦ rv] sitting in [I].  The closure therefore applies the
        wand to reconstitute [r ↦ rv], does its reads, and re-splits with
        [raft_split_trk] before returning.

        [Visit] is told the progress map is [s.(nstate.progress)] and hands
        it back at whatever tracker value it returns; that is what lets the
        final re-seal re-establish [own_raft_phys]'s [Hprs].

        The Goose closure literal reduces to
        [#(func.mk <> "id" (λ: "pr", …))] by the [wp_recc] pure step, so it
        unifies with the spec's [#f] with no help. *)
  Lemma wp_raft__reset : wp_raft__reset_body.
  Proof.
    intros_ambient.
    intros cfg r id s term Hlent.
    wp_start as "Hphys". iNamed "Hphys". wp_auto.
    set (s0 := s <| nstate.term := term |>
                 <| nstate.vote := if decide (term = s.(nstate.term))
                                   then s.(nstate.vote) else W64 0 |>).
    wp_if_join (λ v, ⌜ v = execute_val ⌝ ∗ r_ptr ↦ r ∗ term_ptr ↦ term ∗
                     own_raft_phys cfg r id s0)%I
      with "[r term Hr Htrk Hlog Hmsgs Hmsgs_cap HmsgsAA HmsgsAA_cap Hmisc]".
    (* Two arms: [r.Term != term] writes [Term] and [Vote]; otherwise
       nothing is written and the vote survives.  Both re-seal at [s0]. *)
    1-2: try wp_auto.
    1-2: iSplitR; first done.
    1-2: iFrame "r term".
    1-2: iApply (own_raft_phys_intro _ _ _ s0 with
           "Hr Hlogger Hprs Htrk Hlog Hmsgs Hmsgs_cap HmsgsAA HmsgsAA_cap Hmisc");
         try done.
    (* the vote goal of each arm: split on the [decide] in [s0] *)
    all: try (rewrite /s0 /=; case_decide; congruence).
    iIntros (v) "(-> & r & term & Hphys)".
    iDestruct "Hphys" as (rv1 msgs1 msgsAA1 lok1) "Hphys".
    iNamedSuffix "Hphys" "1".
    wp_auto.
    (* [lead := None], [electionElapsed := 0], [heartbeatElapsed := 0] *)
    set (s1 := s0 <| nstate.lead := W64 0 |>).
    iAssert (own_raft_phys cfg r id s1)
      with "[Hr1 Htrk1 Hlog1 Hmsgs1 Hmsgs_cap1 HmsgsAA1 HmsgsAA_cap1 Hmisc1]"
      as "Hphys".
    { iApply (own_raft_phys_intro _ _ _ (s1) with
        "Hr1 Hlogger1 Hprs1 Htrk1 Hlog1 Hmsgs1 Hmsgs_cap1 HmsgsAA1 HmsgsAA_cap1 Hmisc1");
        done. }
    wp_apply (wp_raft__resetRandomizedElectionTimeout with "[$Hphys]") as "Hphys".
    wp_apply (wp_raft__abortLeaderTransfer with "[$Hphys]") as "Hphys".
    iDestruct "Hphys" as (rv2 msgs2 msgsAA2 lok2) "Hphys".
    iNamedSuffix "Hphys" "2".
    iDestruct (own_raftLog_unless_open _ _ Hlent with "Hlog2") as "Hlog2".
    iDestruct (own_tracker_unless_open _ _ _ _ Hlent with "Htrk2") as "Htrk2".
    iDestruct (raft_split_trk with "Hr2") as "[Htrkf Hrback]".
    wp_apply (wp_ProgressTracker__ResetVotes with "[$Htrkf $Htrk2]")
      as "%votesRef [Htrkf Htrk]".
    (* Do *not* re-assemble here.  [Visit] owns the [trk] field -- it reads
       [p.Progress] through its pointer receiver -- and lends it to the
       closure, so the field has to stay split out and [I] carries the
       continuation wand in place of [r ↦ rv].  The wand stays
       **quantified** over the field value: [Visit] may hand the field back
       at a different tracker value (see [visit_closure], inv_tracker.v),
       so nothing here may fix it. *)
    wp_apply (wp_ProgressTracker__Visit _ _ _ _ s.(nstate.progress) _
                (r_ptr ↦ r ∗
                 own_raftLog rv2.(raft.raft.raftLog') ∗
                 (∀ tvx, r.[raft.raft.t, "trk"] ↦ tvx -∗
                  r ↦ (rv2 <| raft.raft.trk' := tvx |>)))%I
                with "[$Htrkf $Htrk $r $Hlog2 $Hrback $Hprs2]")
      as "(%tvfin & Htrkf & Htrk & #Hprsfin & r & Hlog & Hrback)".
    { (* the [Visit] closure: re-initialise one [Progress] wholesale *)
      iModIntro. iIntros (i pr tv0).
      wp_start as "(%Hicfg & %Hpri & %HmaxI & Htrkf & #Hprsv & Hpr & Hback &
                    r & Hlog & Hrback)".
      (* Keep [Hnolearner]: [own_progress] carries
         [⌜pv.(IsLearner') = false⌝], and the closure has to hand it back.
         The [Progress] literal it writes copies [IsLearner] straight across
         from the old one, so the fact carries over unchanged -- but only if
         it is not dropped here. *)
      iDestruct "Hpr" as (pv ivold) "(Hpv & Hinfl & %Hnolearner & %Hst)".
      (* the closure reads [r.raftLog] and [r.id] as well as
         [r.trk.MaxInflight], so it needs the whole struct back *)
      iDestruct ("Hrback" $! tv0 with "Htrkf") as "Hr".
      wp_auto.
      (* [lastIndex]'s spec is stated at a fixed split, so open
         [own_raftLog] and close it again. *)
      iDestruct (own_raftLog_acc with "Hlog")
        as (lprev0 lsents0 luents0) "[Hlog Hlogback0]".
      wp_apply (wp_raftLog__lastIndex_at with "[$Hlog]")
        as "%li [Hlog %Hli0]".
      iDestruct ("Hlogback0" with "Hlog") as "Hlog".
      wp_apply (wp_tracker_NewInflights _ _ HmaxI) as "%ifl Hifl".
      iDestruct "Hifl" as (ivnew) "Hifl".
      destruct (decide (i = rv2.(raft.raft.id'))) as [Hii|Hii].
      + assert (bool_decide (i = rv2.(raft.raft.id')) = true) as Hbi
          by (apply bool_decide_eq_true_2; done).
        rewrite Hbi /=. wp_auto.
        iDestruct (own_raftLog_acc with "Hlog")
          as (lprev1 lsents1 luents1) "[Hlog Hlogback1]".
        wp_apply (wp_raftLog__lastIndex_at with "[$Hlog]")
          as "%li2 [Hlog %Hli1]".
        iDestruct ("Hlogback1" with "Hlog") as "Hlog".
        (* re-split: [Visit] gets the field back, [I] gets its quantified
           wand back.  [raft_split_trk] hands it back one setter deeper
           ([… <|trk' := tv0|> <|trk' := tvx|>]); the two records are
           convertible -- every other field is copied -- so an [iExact]
           through an explicit [iIntros] retypes it. *)
        iDestruct (raft_split_trk with "Hr") as "[Htrkf Hrback2]".
        iApply "HΦ". iExists tv0.
        iSplitL "Htrkf"; first iExact "Htrkf".
        iSplitL "Hpv Hifl Hback".
        { iApply "Hback". rewrite /own_progress /own_progress_at.
          iExists _, ivnew. iFrame "Hpv". simpl. iFrame "Hifl".
          (* the [Progress] literal has no [State] field, so [State] is the
             zero value [StateProbe]; [IsLearner] is copied across *)
          iPureIntro. split; [ exact Hnolearner | rewrite /progress_state_ok; by left ]. }
        iFrame "Hprsv r Hlog".
        iIntros (tvx) "Hf". iDestruct ("Hrback2" $! tvx with "Hf") as "Hr".
        iExact "Hr".
      + assert (bool_decide (i = rv2.(raft.raft.id')) = false) as Hbi
          by (apply bool_decide_eq_false_2; done).
        rewrite Hbi /=. wp_auto.
        iDestruct (raft_split_trk with "Hr") as "[Htrkf Hrback2]".
        iApply "HΦ". iExists tv0.
        iSplitL "Htrkf"; first iExact "Htrkf".
        iSplitL "Hpv Hifl Hback".
        { iApply "Hback". rewrite /own_progress /own_progress_at.
          iExists _, ivnew. iFrame "Hpv". simpl. iFrame "Hifl".
          iPureIntro. split; [ exact Hnolearner | rewrite /progress_state_ok; by left ]. }
        iFrame "Hprsv r Hlog".
        iIntros (tvx) "Hf". iDestruct ("Hrback2" $! tvx with "Hf") as "Hr".
        iExact "Hr". }
    (* [Visit] hands the field back; re-assemble the struct for the tail *)
    iDestruct ("Hrback" $! tvfin with "Htrkf") as "Hr".
    (* [r.readOnly = newReadOnly(r.readOnly.option)] *)
    iDestruct (own_raft_misc_option with "Hmisc2") as (o) "[Hopt Hmiscback]".
    wp_auto.
    iDestruct ("Hmiscback" with "Hopt") as "Hmisc".
    wp_apply (wp_newReadOnly with "[$Hmisc]") as "%ro' Hmisc".
    iDestruct (own_raftLog_unless_close _ _ Hlent with "Hlog") as "Hlog".
    iDestruct (own_tracker_unless_close _ _ _ _ Hlent with "Htrk") as "Htrk".
    iApply "HΦ".
    iApply (own_raft_phys_intro _ _ _ (reset_to s term) with
      "Hr Hlogger2 Hprsfin Htrk Hlog Hmsgs2 Hmsgs_cap2 HmsgsAA2 HmsgsAA_cap2 Hmisc");
      done.
  Qed.

End ResetProof.
