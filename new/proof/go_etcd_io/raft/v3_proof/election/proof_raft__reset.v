Require Export New.proof.go_etcd_io.raft.v3_proof.election.postulates_raft__reset.

Module ResetProof (P : RESET_POSTULATES) : RESET.

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
      - [trk.Visit f] is given the *whole raft struct* as its caller invariant
        [I]: the closure reads [r.raftLog], [r.trk.MaxInflight],
        [r.trk.MaxInflightBytes] and [r.id], all through the pointer variable
        the enclosing frame holds, so [I] also has to carry that frame slot
        ([r_ptr ↦ r]).  This is exactly why [wp_ProgressTracker__Visit] does
        not ask for [trk ↦ tv].  The Goose closure literal reduces to
        [#(func.mk <> "id" (λ: "pr", …))] by the [wp_recc] pure step, so it
        unifies with the spec's [#f] with no help. *)
  Lemma wp_raft__reset : wp_raft__reset_body.
  Proof.
    intros_ambient.
    intros cfg r id s term.
    wp_start as "Hphys". iNamed "Hphys". wp_auto.
    destruct (decide (term = s.(nstate.term))) as [Heq|Hne].
    - (* the term is unchanged, so the vote survives and the [if] is skipped *)
      assert (bool_decide (rv.(raft.raft.Term') = term) = true) as Hb
        by (apply bool_decide_eq_true_2; congruence).
      rewrite Hb /=. wp_auto.
      wp_apply (wp_raft__resetRandomizedElectionTimeout with "[$Hr]") as "%n Hr".
      wp_apply (wp_raft__abortLeaderTransfer with "[$Hr]") as "Hr".
      iDestruct (raft_split_trk with "Hr") as "[Htrkf Hrback]".
      wp_apply (wp_ProgressTracker__ResetVotes with "[$Htrkf $Htrk]")
        as "%votesRef [Htrkf Htrk]".
      iDestruct ("Hrback" with "Htrkf") as "Hr".
      wp_apply (wp_ProgressTracker__Visit _ _ _ _ _
                  (r_ptr ↦ r ∗
                   r ↦ (rv <| raft.raft.lead' := W64 0 |>
                           <| raft.raft.electionElapsed' := W64 0 |>
                           <| raft.raft.heartbeatElapsed' := W64 0 |>
                           <| raft.raft.randomizedElectionTimeout' := n |>
                           <| raft.raft.leadTransferee' := W64 0 |>
                           <| raft.raft.trk' := rv.(raft.raft.trk')
                                <| tracker.ProgressTracker.Votes' := votesRef |> |>) ∗
                   own_raftLog rv.(raft.raft.raftLog'))%I
                  with "[$Htrk $Hr $r $Hlog]") as "[Htrk (r & Hr & Hlog)]".
      { (* the [Visit] closure: re-initialise one [Progress] wholesale *)
        iModIntro. iIntros (i pr).
        wp_start as "[Hpr (r & Hr & Hlog)]".
        iDestruct "Hpr" as (pv) "[Hpv Hinfl]".
        wp_auto.
        wp_apply (wp_raftLog__lastIndex with "[$Hlog]") as "%li Hlog".
        wp_apply wp_tracker_NewInflights as "%ifl Hifl".
        destruct (decide (i = rv.(raft.raft.id'))) as [Hii|Hii].
        + assert (bool_decide (i = rv.(raft.raft.id')) = true) as Hbi
            by (apply bool_decide_eq_true_2; done).
          rewrite Hbi /=. wp_auto.
          wp_apply (wp_raftLog__lastIndex with "[$Hlog]") as "%li2 Hlog".
          iApply "HΦ". iSplitL "Hpv Hifl".
          { rewrite /own_progress. iExists _. iFrame "Hpv". simpl. iFrame "Hifl". }
          iFrame.
        + assert (bool_decide (i = rv.(raft.raft.id')) = false) as Hbi
            by (apply bool_decide_eq_false_2; done).
          rewrite Hbi /=. wp_auto.
          iApply "HΦ". iSplitL "Hpv Hifl".
          { rewrite /own_progress. iExists _. iFrame "Hpv". simpl. iFrame "Hifl". }
          iFrame. }
      (* [r.readOnly = newReadOnly(r.readOnly.option)] *)
      iDestruct (own_raft_misc_option with "Hmisc") as (o) "[Hopt Hmiscback]".
      wp_auto.
      iDestruct ("Hmiscback" with "Hopt") as "Hmisc".
      wp_apply (wp_newReadOnly with "[$Hmisc]") as "%ro' Hmisc".
      iApply "HΦ". rewrite /own_raft_phys.
      iExists _, msgs, msgsAA, lok. iFrame "Hr". simpl. iFrame "∗#%".
      iPureIntro. split_and!; congruence.
    - (* the term changes, so [Term] is written and the vote cleared *)
      assert (bool_decide (rv.(raft.raft.Term') = term) = false) as Hb
        by (apply bool_decide_eq_false_2; congruence).
      rewrite Hb /=. wp_auto.
      wp_apply (wp_raft__resetRandomizedElectionTimeout with "[$Hr]") as "%n Hr".
      wp_apply (wp_raft__abortLeaderTransfer with "[$Hr]") as "Hr".
      iDestruct (raft_split_trk with "Hr") as "[Htrkf Hrback]".
      wp_apply (wp_ProgressTracker__ResetVotes with "[$Htrkf $Htrk]")
        as "%votesRef [Htrkf Htrk]".
      iDestruct ("Hrback" with "Htrkf") as "Hr".
      wp_apply (wp_ProgressTracker__Visit _ _ _ _ _
                  (r_ptr ↦ r ∗
                   r ↦ (rv <| raft.raft.Term' := term |>
                           <| raft.raft.Vote' := W64 0 |>
                           <| raft.raft.lead' := W64 0 |>
                           <| raft.raft.electionElapsed' := W64 0 |>
                           <| raft.raft.heartbeatElapsed' := W64 0 |>
                           <| raft.raft.randomizedElectionTimeout' := n |>
                           <| raft.raft.leadTransferee' := W64 0 |>
                           <| raft.raft.trk' := rv.(raft.raft.trk')
                                <| tracker.ProgressTracker.Votes' := votesRef |> |>) ∗
                   own_raftLog rv.(raft.raft.raftLog'))%I
                  with "[$Htrk $Hr $r $Hlog]") as "[Htrk (r & Hr & Hlog)]".
      { iModIntro. iIntros (i pr).
        wp_start as "[Hpr (r & Hr & Hlog)]".
        iDestruct "Hpr" as (pv) "[Hpv Hinfl]".
        wp_auto.
        wp_apply (wp_raftLog__lastIndex with "[$Hlog]") as "%li Hlog".
        wp_apply wp_tracker_NewInflights as "%ifl Hifl".
        destruct (decide (i = rv.(raft.raft.id'))) as [Hii|Hii].
        + assert (bool_decide (i = rv.(raft.raft.id')) = true) as Hbi
            by (apply bool_decide_eq_true_2; done).
          rewrite Hbi /=. wp_auto.
          wp_apply (wp_raftLog__lastIndex with "[$Hlog]") as "%li2 Hlog".
          iApply "HΦ". iSplitL "Hpv Hifl".
          { rewrite /own_progress. iExists _. iFrame "Hpv". simpl. iFrame "Hifl". }
          iFrame.
        + assert (bool_decide (i = rv.(raft.raft.id')) = false) as Hbi
            by (apply bool_decide_eq_false_2; done).
          rewrite Hbi /=. wp_auto.
          iApply "HΦ". iSplitL "Hpv Hifl".
          { rewrite /own_progress. iExists _. iFrame "Hpv". simpl. iFrame "Hifl". }
          iFrame. }
      iDestruct (own_raft_misc_option with "Hmisc") as (o) "[Hopt Hmiscback]".
      wp_auto.
      iDestruct ("Hmiscback" with "Hopt") as "Hmisc".
      wp_apply (wp_newReadOnly with "[$Hmisc]") as "%ro' Hmisc".
      iApply "HΦ". rewrite /own_raft_phys.
      iExists _, msgs, msgsAA, lok. iFrame "Hr". simpl. iFrame "∗#%".
      iPureIntro. split_and!; congruence.
  Qed.

End ResetProof.
