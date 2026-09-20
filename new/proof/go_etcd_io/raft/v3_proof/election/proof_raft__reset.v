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

      Two things structure the proof.

      - The Go code branches on [r.Term != term], and the model's [reset]
        keeps the vote exactly when the term is unchanged, so the proof
        case-splits on [decide (term = s.(nstate.term))] and runs the same
        script twice.  The two arms differ only in the struct value (the
        second sets [Term'] and [Vote']) and in the final pure goals, which is
        why they are spelled out rather than shared.
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
        [raft_split_trk] before returning.  Until 2026-09-16
        [wp_ProgressTracker__Visit] asked for no part of the tracker struct
        at all and a comment there explained why it did not need to; the
        comment was wrong and the statement was false.  See that lemma.

        The Goose closure literal reduces to
        [#(func.mk <> "id" (λ: "pr", …))] by the [wp_recc] pure step, so it
        unifies with the spec's [#f] with no help. *)
  Lemma wp_raft__reset : wp_raft__reset_body.
  Proof.
    intros_ambient.
    intros cfg r id s term f.
    wp_start as "Hphys". iNamed "Hphys". wp_auto.
    destruct (decide (term = s.(nstate.term))) as [Heq|Hne].
    - (* the term is unchanged, so the vote survives and the [if] is skipped *)
      assert (bool_decide (rv.(raft.raft.Term') = term) = true) as Hb
        by (apply bool_decide_eq_true_2; congruence).
      rewrite Hb /=. wp_auto.
      (* The lemma's [rv] must be the struct *as the heap now holds it* -- the
         three writes above have happened.  Handing it [HelectionTimeout]
         directly does not work either way round: the hypothesis is stated at
         the bare [rv], so unifying against it either picks the pre-update
         struct (and [iFrame] then cannot find [r ↦ …]) or, when the struct is
         given explicitly, solves the still-unresolved [Setter] instance evar
         by the degenerate [λ _ _, rv] -- a term convertible to but not
         syntactically the setter chain in [Hr], which [iFrame] again rejects.
         So establish the premise at the updated struct first, with its own
         elaboration: [electionTimeout'] is untouched by the setters, so
         [HelectionTimeout] proves it by conversion. *)
      assert (0 < sint.Z (rv <| raft.raft.lead' := W64 0 |>
                             <| raft.raft.electionElapsed' := W64 0 |>
                             <| raft.raft.heartbeatElapsed' := W64 0 |>)
                           .(raft.raft.electionTimeout')) as Het
        by exact HelectionTimeout.
      wp_apply (wp_raft__resetRandomizedElectionTimeout _ _ Het with "[$Hr]")
        as "%n Hr". clear Het.
      wp_apply (wp_raft__abortLeaderTransfer with "[$Hr]") as "Hr".
      iDestruct (raft_split_trk with "Hr") as "[Htrkf Hrback]".
      wp_apply (wp_ProgressTracker__ResetVotes with "[$Htrkf $Htrk]")
        as "%votesRef [Htrkf Htrk]".
      (* Do *not* re-assemble here.  [Visit] owns the [trk] field -- it reads
         [p.Progress] through its pointer receiver -- and lends it to the
         closure, so the field has to stay split out and [I] carries the
         continuation wand in place of [r ↦ rv].  Specialising the wand now
         fixes the field value it expects to the one [ResetVotes] installed. *)
      iSpecialize ("Hrback" $! (rv.(raft.raft.trk')
                     <| tracker.ProgressTracker.Votes' := votesRef |>)).
      wp_apply (wp_ProgressTracker__Visit _ _ _ _ _
                  (r_ptr ↦ r ∗
                   own_raftLog rv.(raft.raft.raftLog') ∗
                   (r.[raft.raft.t, "trk"] ↦ (rv.(raft.raft.trk')
                        <| tracker.ProgressTracker.Votes' := votesRef |>) -∗
                    r ↦ (rv <| raft.raft.lead' := W64 0 |>
                            <| raft.raft.electionElapsed' := W64 0 |>
                            <| raft.raft.heartbeatElapsed' := W64 0 |>
                            <| raft.raft.randomizedElectionTimeout' := n |>
                            <| raft.raft.leadTransferee' := W64 0 |>
                            <| raft.raft.trk' := rv.(raft.raft.trk')
                                 <| tracker.ProgressTracker.Votes' := votesRef |> |>)))%I
                  with "[$Htrkf $Htrk $r $Hlog $Hrback]")
        as "(Htrkf & Htrk & r & Hlog & Hrback)".
      { (* the [Visit] closure: re-initialise one [Progress] wholesale *)
        iModIntro. iIntros (i pr).
        wp_start as "(Htrkf & Hpr & r & Hlog & Hrback)".
        (* Keep [Hnolearner]: [own_progress] carries
           [⌜pv.(IsLearner') = false⌝] since 2026-09-16, and the closure has
           to hand it back.  The [Progress] literal it writes copies
           [IsLearner] straight across from the old one, so the fact carries
           over unchanged -- but only if it is not dropped here. *)
        iDestruct "Hpr" as (pv) "(Hpv & Hinfl & %Hnolearner)".
        (* the closure reads [r.raftLog] and [r.id] as well as
           [r.trk.MaxInflight], so it needs the whole struct back *)
        iDestruct ("Hrback" with "Htrkf") as "Hr".
        wp_auto.
        (* [lastIndex]'s spec is stated at a fixed split, so open
           [own_raftLog] and close it again. *)
        iDestruct (own_raftLog_acc with "Hlog")
          as (lprev0 lsents0 luents0) "[Hlog Hlogback0]".
        wp_apply (wp_raftLog__lastIndex_at with "[$Hlog]")
          as "%li [Hlog %Hli0]".
        iDestruct ("Hlogback0" with "Hlog") as "Hlog".
        wp_apply wp_tracker_NewInflights as "%ifl Hifl".
        destruct (decide (i = rv.(raft.raft.id'))) as [Hii|Hii].
        + assert (bool_decide (i = rv.(raft.raft.id')) = true) as Hbi
            by (apply bool_decide_eq_true_2; done).
          rewrite Hbi /=. wp_auto.
          (* [lastIndex]'s spec is stated at a fixed split, so open
             [own_raftLog] and close it again. *)
          iDestruct (own_raftLog_acc with "Hlog")
            as (lprev1 lsents1 luents1) "[Hlog Hlogback1]".
          wp_apply (wp_raftLog__lastIndex_at with "[$Hlog]")
            as "%li2 [Hlog %Hli1]".
          iDestruct ("Hlogback1" with "Hlog") as "Hlog".
          (* re-split: [Visit] gets the field back, [I] gets its wand back *)
          iDestruct (raft_split_trk_id with "Hr") as "[Htrkf Hrback]".
          iApply "HΦ". iSplitL "Htrkf"; first iExact "Htrkf".
          iSplitL "Hpv Hifl".
          { rewrite /own_progress. iExists _. iFrame "Hpv". simpl.
            iFrame "Hifl". iPureIntro. exact Hnolearner. }
          iFrame "r Hlog". iExact "Hrback".
        + assert (bool_decide (i = rv.(raft.raft.id')) = false) as Hbi
            by (apply bool_decide_eq_false_2; done).
          rewrite Hbi /=. wp_auto.
          iDestruct (raft_split_trk_id with "Hr") as "[Htrkf Hrback]".
          iApply "HΦ". iSplitL "Htrkf"; first iExact "Htrkf".
          iSplitL "Hpv Hifl".
          { rewrite /own_progress. iExists _. iFrame "Hpv". simpl.
            iFrame "Hifl". iPureIntro. exact Hnolearner. }
          iFrame "r Hlog". iExact "Hrback". }
      (* [Visit] hands the field back; re-assemble the struct for the tail *)
      iDestruct ("Hrback" with "Htrkf") as "Hr".
      (* [r.readOnly = newReadOnly(r.readOnly.option)] *)
      iDestruct (own_raft_misc_option with "Hmisc") as (o) "[Hopt Hmiscback]".
      wp_auto.
      iDestruct ("Hmiscback" with "Hopt") as "Hmisc".
      wp_apply (wp_newReadOnly with "[$Hmisc]") as "%ro' Hmisc".
      iApply "HΦ". rewrite /own_raft_phys_at.
      iExists _, msgs, msgsAA, lok. iFrame "Hr". simpl. iFrame "∗#%".
      iPureIntro. split_and!; congruence.
    - (* the term changes, so [Term] is written and the vote cleared *)
      assert (bool_decide (rv.(raft.raft.Term') = term) = false) as Hb
        by (apply bool_decide_eq_false_2; congruence).
      rewrite Hb /=. wp_auto.
      (* As in the first arm, but the heap value also carries the [Term] and
         [Vote] writes this branch performed. *)
      assert (0 < sint.Z (rv <| raft.raft.Term' := term |>
                             <| raft.raft.Vote' := W64 0 |>
                             <| raft.raft.lead' := W64 0 |>
                             <| raft.raft.electionElapsed' := W64 0 |>
                             <| raft.raft.heartbeatElapsed' := W64 0 |>)
                           .(raft.raft.electionTimeout')) as Het
        by exact HelectionTimeout.
      wp_apply (wp_raft__resetRandomizedElectionTimeout _ _ Het with "[$Hr]")
        as "%n Hr". clear Het.
      wp_apply (wp_raft__abortLeaderTransfer with "[$Hr]") as "Hr".
      iDestruct (raft_split_trk with "Hr") as "[Htrkf Hrback]".
      wp_apply (wp_ProgressTracker__ResetVotes with "[$Htrkf $Htrk]")
        as "%votesRef [Htrkf Htrk]".
      (* Do *not* re-assemble here.  [Visit] owns the [trk] field -- it reads
         [p.Progress] through its pointer receiver -- and lends it to the
         closure, so the field has to stay split out and [I] carries the
         continuation wand in place of [r ↦ rv].  Specialising the wand now
         fixes the field value it expects to the one [ResetVotes] installed. *)
      iSpecialize ("Hrback" $! (rv.(raft.raft.trk')
                     <| tracker.ProgressTracker.Votes' := votesRef |>)).
      wp_apply (wp_ProgressTracker__Visit _ _ _ _ _
                  (r_ptr ↦ r ∗
                   own_raftLog rv.(raft.raft.raftLog') ∗
                   (r.[raft.raft.t, "trk"] ↦ (rv.(raft.raft.trk')
                        <| tracker.ProgressTracker.Votes' := votesRef |>) -∗
                    r ↦ (rv <| raft.raft.Term' := term |>
                            <| raft.raft.Vote' := W64 0 |>
                            <| raft.raft.lead' := W64 0 |>
                            <| raft.raft.electionElapsed' := W64 0 |>
                            <| raft.raft.heartbeatElapsed' := W64 0 |>
                            <| raft.raft.randomizedElectionTimeout' := n |>
                            <| raft.raft.leadTransferee' := W64 0 |>
                            <| raft.raft.trk' := rv.(raft.raft.trk')
                                 <| tracker.ProgressTracker.Votes' := votesRef |> |>)))%I
                  with "[$Htrkf $Htrk $r $Hlog $Hrback]")
        as "(Htrkf & Htrk & r & Hlog & Hrback)".
      { iModIntro. iIntros (i pr).
        wp_start as "(Htrkf & Hpr & r & Hlog & Hrback)".
        (* Keep [Hnolearner]: [own_progress] carries
           [⌜pv.(IsLearner') = false⌝] since 2026-09-16, and the closure has
           to hand it back.  The [Progress] literal it writes copies
           [IsLearner] straight across from the old one, so the fact carries
           over unchanged -- but only if it is not dropped here. *)
        iDestruct "Hpr" as (pv) "(Hpv & Hinfl & %Hnolearner)".
        (* the closure reads [r.raftLog] and [r.id] as well as
           [r.trk.MaxInflight], so it needs the whole struct back *)
        iDestruct ("Hrback" with "Htrkf") as "Hr".
        wp_auto.
        (* [lastIndex]'s spec is stated at a fixed split, so open
           [own_raftLog] and close it again. *)
        iDestruct (own_raftLog_acc with "Hlog")
          as (lprev2 lsents2 luents2) "[Hlog Hlogback2]".
        wp_apply (wp_raftLog__lastIndex_at with "[$Hlog]")
          as "%li [Hlog %Hli2]".
        iDestruct ("Hlogback2" with "Hlog") as "Hlog".
        wp_apply wp_tracker_NewInflights as "%ifl Hifl".
        destruct (decide (i = rv.(raft.raft.id'))) as [Hii|Hii].
        + assert (bool_decide (i = rv.(raft.raft.id')) = true) as Hbi
            by (apply bool_decide_eq_true_2; done).
          rewrite Hbi /=. wp_auto.
          (* [lastIndex]'s spec is stated at a fixed split, so open
             [own_raftLog] and close it again. *)
          iDestruct (own_raftLog_acc with "Hlog")
            as (lprev3 lsents3 luents3) "[Hlog Hlogback3]".
          wp_apply (wp_raftLog__lastIndex_at with "[$Hlog]")
            as "%li2 [Hlog %Hli3]".
          iDestruct ("Hlogback3" with "Hlog") as "Hlog".
          (* re-split: [Visit] gets the field back, [I] gets its wand back *)
          iDestruct (raft_split_trk_id with "Hr") as "[Htrkf Hrback]".
          iApply "HΦ". iSplitL "Htrkf"; first iExact "Htrkf".
          iSplitL "Hpv Hifl".
          { rewrite /own_progress. iExists _. iFrame "Hpv". simpl.
            iFrame "Hifl". iPureIntro. exact Hnolearner. }
          iFrame "r Hlog". iExact "Hrback".
        + assert (bool_decide (i = rv.(raft.raft.id')) = false) as Hbi
            by (apply bool_decide_eq_false_2; done).
          rewrite Hbi /=. wp_auto.
          iDestruct (raft_split_trk_id with "Hr") as "[Htrkf Hrback]".
          iApply "HΦ". iSplitL "Htrkf"; first iExact "Htrkf".
          iSplitL "Hpv Hifl".
          { rewrite /own_progress. iExists _. iFrame "Hpv". simpl.
            iFrame "Hifl". iPureIntro. exact Hnolearner. }
          iFrame "r Hlog". iExact "Hrback". }
      (* [Visit] hands the field back; re-assemble the struct for the tail *)
      iDestruct ("Hrback" with "Htrkf") as "Hr".
      iDestruct (own_raft_misc_option with "Hmisc") as (o) "[Hopt Hmiscback]".
      wp_auto.
      iDestruct ("Hmiscback" with "Hopt") as "Hmisc".
      wp_apply (wp_newReadOnly with "[$Hmisc]") as "%ro' Hmisc".
      iApply "HΦ". rewrite /own_raft_phys_at.
      iExists _, msgs, msgsAA, lok. iFrame "Hr". simpl. iFrame "∗#%".
      iPureIntro. split_and!; congruence.
  Qed.

End ResetProof.
