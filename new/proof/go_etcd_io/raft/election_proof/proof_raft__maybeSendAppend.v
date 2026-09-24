Require Export New.proof.go_etcd_io.raft.election_proof.postulates_raft__maybeSendAppend.

Module RaftMaybeSendAppendProof (P : RAFT__MAYBESENDAPPEND_POSTULATES)
  : RAFT__MAYBESENDAPPEND.
Import P.

Section helpers.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : raft.Assumptions}.
Collection W := sem + package_sem.
Set Default Proof Using "W".

Context (cfg : gset w64).

(** Lend an empty page.  On the arm where [raftLog.entries] is *not*
    called, [ents] stays the zero slice; lending it as a page puts the log
    in the same state as on the two arms that fetch one, which is what lets
    one script serve all three. *)
Local Lemma own_raftLog_lend_nil l prev sents uents cm ap :
  own_raftLog l (logstate.mk prev sents uents cm ap None) -∗
  own_raftLog l (logstate.mk prev sents uents cm ap (Some (slice.nil, [], DfracOwn 1))).
Proof.
  iIntros "H". iNamed "H".
  iApply (own_raftLog_lend_page with "Hl [//] [//]").
  iIntros "_". iExact "Hcore".
Qed.

(** ** What the three arms of [pr.State != StateReplicate || !pr.Inflights.Full()]
       have in common

    The [if] has three outcomes -- not in [StateReplicate]; in it with room
    in the window; in it with the window full -- and the first two run
    [r.raftLog.entries] while the third leaves [ents] at the zero slice.
    Everything after the [if] is the same program, so the three are brought
    to a common state and the rest of the proof is written once (the three
    goals are discharged by one [;]-chained script below).

    The first three existentials are the page: where it is, what is in it,
    at what fraction.  The log is on loan of that page ([logstate.page]).
    On the third arm the page is [slice.nil], [[]], [DfracOwn 1]
    ([own_raftLog_lend_nil]), and rebinding the zero slice to a variable is
    what makes that arm's *program text* match the other two's, which is
    what lets one script serve all three.  The fourth is the [raftLog]
    record, held out of the log ([own_raftLog_struct]) because the message
    literal and [SentCommit] read [r.raftLog.committed] through it; [Hlb]
    puts it back.  [Hwin] is
    [Progress.SentEntries]'s second premise in the only form all three arms
    can supply it: entries are fetched only when the window has room, so a
    non-empty page in [StateReplicate] means the window was not full -- and
    nothing between the test and [SentEntries] touches the window. *)
Definition msa_pkg (ep lgp : loc) (pv : tracker.Progress.t)
    (iv : tracker.Inflights.t) (ls : logstate.t) : iProp Σ :=
  ∃ (sl : slice.t) (es : list raftpb.Entry.t) (dq : dfrac)
    (lv : raft.raftLog.t),
  "ents" ∷ ep ↦ sl ∗
  "Hl" ∷ lgp ↦ lv ∗
  "Hpage" ∷ sl ↦*{dq} es ∗
  "Hlb" ∷ (lgp ↦ lv -∗ own_raftLog lgp (ls <| logstate.page := Some (sl, es, dq) |>)) ∗
  "%Hwin" ∷ ⌜ pv.(tracker.Progress.State') = W64 1 → es ≠ [] →
              inflights_full iv = false ⌝.

(** [MsgApp] is one of the four types the model describes, so [send_ok]'s
    *second* clause applies: the message goes out at [r.Term]. *)
Local Lemma mtype_of_MsgApp : mtype_of MsgApp = Some mtype.App.
Proof.
  rewrite /mtype_of.
  case_decide as H1. { exfalso. rewrite /MsgApp /MsgVote in H1. word. }
  case_decide as H2. { exfalso. rewrite /MsgApp /MsgVoteResp in H2. word. }
  case_decide as H3; [done|congruence].
Qed.

End helpers.

Set Default Proof Using "Type".

  (* End the loan, and get from the state [own_raft_phys_unlend] names back
     to [s]. *)
  Local Ltac finish s Hlent :=
    iDestruct (own_raft_phys_unlend with "Hphys Htrk Hlog") as "Hphys";
    [ done | ];
    iDestruct (own_raft_phys_eq _ _ _ _ s with "Hphys") as "Hphys";
    [ destruct s; simpl in Hlent; subst; done | ].

  (** [r.maybeSendAppend(to, sendIfEmpty)]
      ([raft__maybeSendAppendⁱᵐᵖˡ], new/code/go_etcd_io/raft/v3.v:3096).

      **What is held across [r.send(...)].**  Two things read out of the
      struct: one voter's [Progress], borrowed out of [own_tracker] --
      [pr.SentEntries] needs what this proof learned about it before the
      send -- and one page of entries, borrowed out of [own_raftLog] by
      [raftLog.entries] -- [payloadsSize] reads it after the send.  So the
      tracker's heap and the log are **lent** out of the struct for the
      whole body ([own_raft_phys_lend]; [nstate.lent], [defs.v]), and every
      raft field read, and the [send], is made on [own_raft_phys] at the
      lent state.  [own_raft_phys_unlend] ends the loan on each exit
      ([finish] for the exits that send nothing).  [raftLog.entries] hands
      the [raftLog] *record* back alongside the page, which is what makes
      the literal's [Commit: r.raftLog.committed] steppable while the page
      is out.  (From 2026-09-21 to 2026-09-22 the same thing was done with a
      variant predicate, [own_raft_bare].)


      [maybeSendSnapshot] needs neither: on that exit the [Progress] goes
      back into the tracker first, and the callee borrows it again by its
      key in [s.(nstate.progress)].

      The script, following the body:

      - [pr := r.trk.Progress[to]] hits because [to ∈ cfg]: take the
        (persistent) progress map out with [own_tracker_progress_map], step
        the lookup with [wp_map_lookup1], and borrow the [own_progress] with
        [own_tracker_lookup].  The borrow is returned exactly once, at
        whichever exit is taken.
      - [pr.IsPaused()]: on [true], return [false] having sent nothing; on
        [false] the answer [progress_paused pv = false] gives
        [pv.State ≠ StateSnapshot], which is [SentEntries]'s first premise.
      - [r.raftLog.term(pr.Next-1)] at the log's state.  On an error
        (the [interface.ok] case), [maybeSendSnapshot], whose postcondition
        is at the same abstract state -- [MsgSnap] is model-invisible.  On
        [interface.nil], the iff of [spec_raftLog__term.v] gives
        [prev.index ≤ pr.Next - 1], and with [own_raftLog_core]'s [Hnowrap]
        that is [prev.index + 1 ≤ pr.Next]: [pr.Next = 0] is excluded
        because then the argument is [2^64 - 1], which the range puts out of
        bounds.  That inequality is [raftLog.entries]'s only premise.
      - the [||] and its three arms: see [msa_pkg] above.
      - [len(ents) == 0 && !sendIfEmpty] returns [false].
      - the second [if err != nil] is dead: [err] is [interface.nil] from
        the [term] call, and [raftLog.entries] returns [interface.nil] too.
      - [r.send(pb.Message{To: to, Type: MsgApp, ...})] with [send_ok]'s
        second clause: [Term] is unset in the literal, [To = to ≠ id], and
        [out = [msg.mk mtype.App id to s.term false]], which is
        [app_sends].
      - [SentEntries(len ents, payloadsSize ents)] and
        [SentCommit(r.raftLog.committed)], then [return true]. *)
  Lemma wp_raft__maybeSendAppend : wp_raft__maybeSendAppend_body.
  Proof.
    intros_ambient.
    intros cfg r id s to sendIfEmpty Hto Hcfg Hlent.
    wp_start_folded as "Hphys".
    (* lend the tracker and the log before the body is in the goal *)
    (* the [iNamed] only strips the precondition's name *)
    iNamed "Hphys".
    iDestruct (own_raft_phys_lend _ _ _ _ Hlent with "Hphys")
      as (tv ls Hls) "(Htrk & Hlog & Hphys)".
    iDestruct (own_tracker_progress_map with "Htrk") as "(#Hprs & %Hdom & Htrk)".
    assert (is_Some (s.(nstate.progress) !! to)) as [pr Hlk].
    { apply elem_of_dom. rewrite Hdom //. }
    iDestruct (own_tracker_lookup _ _ _ _ _ _ Hlk with "Htrk") as "[Hpr Hprback]".
    (* [r.trk.Progress] is read through the tracker field *)
    iDestruct (own_raft_phys_trk_lent with "Hphys") as "[Htrkf Htrkback]".
    wp_start_unfold.
    wp_auto.
    iDestruct ("Htrkback" with "Htrkf") as "Hphys".
    wp_apply (wp_map_lookup1 with "Hprs") as "_".
    rewrite Hlk /=.
    iDestruct "Hpr" as (pv iv) "Hpa".
    wp_apply (wp_Progress__IsPaused with "[$Hpa]") as "Hpa".
    destruct (progress_paused pv) eqn:Hpaused.
    { (* paused: nothing is sent, [false] *)
      wp_auto.
      iAssert (∃ pv iv, own_progress pr pv iv)%I with "[Hpa]" as "Hpr";
        first by iExists _, _.
      iDestruct ("Hprback" with "Hpr") as "Htrk".
      finish s Hlent.
      iDestruct (own_raft_phys_send_nil with "Hphys") as "Hphys".
      iApply ("HΦ" $! false []). iFrame "Hphys". iPureIntro. constructor. }
    (* not paused, so not in [StateSnapshot] -- [SentEntries]' first premise *)
    assert (Hnosnap : pv.(tracker.Progress.State') ≠ W64 2).
    { intros Hc. rewrite /progress_paused decide_True // in Hpaused. }
    iNamed "Hpa".
    wp_auto. wp_raft_field.
    (* [r.raftLog.term(pr.Next - 1)] *)
    destruct ls as [prev sents uents lcm lap lpg]; logstate_simpl; subst lpg.
    iDestruct (own_raftLog_nowrap with "Hlog") as "[%Hnw Hlog]"; first done.
    cbn [logstate.prev logstate.sents logstate.uents] in Hnw.
    wp_apply (wp_raftLog__term _ (logstate.mk prev sents uents lcm lap None) _ eq_refl with "[$Hlog]")
      as "%pterm %err [Hlog %Herr]".
    cbn [logstate.prev logstate.sents logstate.uents] in Herr.
    destruct err as [eok|].
    { (* the log no longer has [pr.Next - 1]: fall back to a snapshot.
         [wp_pure] first: [wp_auto] alone will not step the
         [Convert go.untyped_bool] in front of the [err != nil] test. *)
      wp_pure. wp_auto.
      iAssert (∃ pv iv, own_progress pr pv iv)%I with "[Hpv Hinfl]" as "Hpr".
      { iExists pv, iv. rewrite /own_progress. iFrame "∗%". }
      (* the [Progress] goes back first: [maybeSendSnapshot] borrows it
         again by its key *)
      iDestruct ("Hprback" with "Hpr") as "Htrk".
      finish s Hlent.
      wp_apply (P.wp_raft__maybeSendSnapshot _ _ _ _ _ _ Hto Hlk Hlent
                  with "[$Hphys]") as "%b Hphys".
      try wp_auto.
      iDestruct (own_raft_phys_send_nil with "Hphys") as "Hphys".
      iApply ("HΦ" $! b []). iFrame "Hphys". iPureIntro. constructor. }
    (* [err = nil]: the iff gives [pr.Next] a lower bound against the log *)
    destruct Herr as [Herr1 _]. specialize (Herr1 eq_refl).
    assert (Hlo : (uint.Z prev.(raft.entryID.index') + 1
                   ≤ uint.Z pv.(tracker.Progress.Next'))%Z) by word.
    wp_pure. wp_auto.
    (* the three arms of the [||], each ending at [msa_pkg] *)
    destruct (decide (pv.(tracker.Progress.State') = W64 1)) as [Hrep|Hnrep];
    [ rewrite bool_decide_eq_true_2 //; wp_auto;
      iDestruct "Hinfl" as (ibuf) "Hinfl";
      wp_apply (wp_Inflights__Full with "[$Hinfl]") as "Hinfl";
      destruct (inflights_full iv) eqn:Hfull;
      [ (* in [StateReplicate] with the window full: no entries are fetched,
           and the log stays whole -- open it just far enough to read
           [committed] later *)
        iDestruct (own_raftLog_lend_nil with "Hlog") as "Hlog";
        iDestruct (own_raftLog_struct with "Hlog") as (lvo) "(Hl & _ & Hlb0)";
        iAssert (msa_pkg ents_ptr s.(nstate.log) pv iv (logstate.mk prev sents uents lcm lap None))
          with "[ents Hl Hlb0]" as "HC";
        [ rewrite /msa_pkg; iExists slice.nil, [], (DfracOwn 1), lvo;
          iFrame "ents Hl";
          iSplitR; [ iApply own_slice_nil | ];
          iSplitL "Hlb0"; [ iExact "Hlb0" | ];
          iPureIntro; intros _ Hne; exfalso; exact (Hne eq_refl)
        | ]
      | (* in [StateReplicate] with room: fetch a page *)
        wp_auto;
        wp_apply (wp_raft_load_maxMsgSize with "Hphys") as "%mms Hphys";
        wp_raft_field;
        wp_apply (wp_raftLog__entries _ (logstate.mk prev sents uents lcm lap None) _ _ eq_refl Hlo with "[$Hlog]")
          as "%sl_e %es_e %dq_e (Hlog & Hpage)";
        iDestruct (own_raftLog_struct with "Hlog") as (lv_e) "(Hl & _ & Hlogback2)";
        try wp_auto;
        iAssert (msa_pkg ents_ptr s.(nstate.log) pv iv (logstate.mk prev sents uents lcm lap None))
          with "[ents Hl Hpage Hlogback2]" as "HC";
        [ rewrite /msa_pkg; iExists sl_e, es_e, dq_e, lv_e; iFrame;
          iPureIntro; intros _ _; exact Hfull | ] ]
    | (* not in [StateReplicate]: the first disjunct is true, fetch a page *)
      rewrite bool_decide_eq_false_2 //; wp_auto;
      wp_apply (wp_raft_load_maxMsgSize with "Hphys") as "%mms Hphys";
      wp_raft_field;
      wp_apply (wp_raftLog__entries _ (logstate.mk prev sents uents lcm lap None) _ _ eq_refl Hlo with "[$Hlog]")
        as "%sl_e %es_e %dq_e (Hlog & Hpage)";
      iDestruct (own_raftLog_struct with "Hlog") as (lv_e) "(Hl & _ & Hlogback2)";
      try wp_auto;
      iAssert (msa_pkg ents_ptr s.(nstate.log) pv iv (logstate.mk prev sents uents lcm lap None))
        with "[ents Hl Hpage Hlogback2]" as "HC";
      [ rewrite /msa_pkg; iExists sl_e, es_e, dq_e, lv_e; iFrame;
        iPureIntro; intros Hc; contradiction | ] ];
    (* --- three goals from here on, in the same state; the rest of the
           proof is one tactic, parenthesised so that it runs once per goal
           (in Ltac1 [A; [b|c]] counts *all* open goals, not the ones the
           previous step made) --- *)
    (iEval (rewrite /msa_pkg) in "HC"; iNamed "HC"; try wp_auto;
    iDestruct (slice_len_Z with "Hpage") as %Hlen;
    (* [if len(ents) == 0 && !sendIfEmpty { return false }] *)
    case_bool_decide as Hc1;
    [ wp_auto; destruct sendIfEmpty;
      [ wp_auto
      | (* an empty page and the caller does not want an empty append *)
        wp_auto;
        iDestruct ("Hlb" with "Hl") as "Hlog";
        iDestruct (own_raftLog_return_page with "Hlog Hpage") as "Hlog"; [ done | ];
        iAssert (∃ pv iv, own_progress pr pv iv)%I with "[Hpv Hinfl]" as "Hpr";
        [ iExists pv, iv; rewrite /own_progress; iFrame "∗%" | ];
        iDestruct ("Hprback" with "Hpr") as "Htrk";
        finish s Hlent;
        iDestruct (own_raft_phys_send_nil with "Hphys") as "Hphys";
        iApply ("HΦ" $! false []); iFrame "Hphys"; iPureIntro;
        rewrite /app_sends; apply Forall_nil_2 ]
    | wp_auto ];
    (* --- the message goes out; again once per goal --- *)
    (* the literal reads [r.raftLog.committed] through [Hl] *)
    (try wp_auto; wp_raft_field;
    wp_apply (P.wp_raft__send with "[$Hphys]");
      [ done
      | right; left; exists mtype.App; split_and!;
        [ by left | apply mtype_of_MsgApp | done | exact Hto | done ]
      | ];
    iIntros "Hphys";
    try wp_auto;
    wp_apply (wp_payloadsSize with "[$Hpage]") as "%psz [Hpage _]";
    iAssert (own_progress pr pv iv) with "[Hpv Hinfl]" as "Hpa";
    [ rewrite /own_progress; iFrame "∗%" | ];
    assert (Hwin2 : pv.(tracker.Progress.State') = W64 1 →
                    (0 < sint.Z sl.(slice.len))%Z → inflights_full iv = false);
    [ intros H1 H2; apply Hwin; [exact H1|]; intros Heq; rewrite Heq in Hlen;
      simpl in Hlen; lia | ];
    wp_apply (wp_Progress__SentEntries _ _ _ _ _ Hnosnap Hwin2 with "[$Hpa]")
      as "Hpr";
    try wp_auto; wp_raft_field;
    iDestruct "Hpr" as (pv3 iv3) "Hpa3";
    wp_apply (wp_Progress__SentCommit with "[$Hpa3]") as "Hpa3";
    try wp_auto;
    iDestruct ("Hlb" with "Hl") as "Hlog";
    iDestruct (own_raftLog_return_page with "Hlog Hpage") as "Hlog"; [ done | ];
    iAssert (∃ pv iv, own_progress pr pv iv)%I with "[Hpa3]" as "Hpr";
    [ by iExists _, _ | ];
    iDestruct ("Hprback" with "Hpr") as "Htrk";
    (* end the loan: [send] changed the outbox, so first put the state in
       the form [own_raft_phys_unlend] takes *)
    iDestruct (own_raft_phys_eq _ _ _ _
                 ((send_msgs s [msg.mk mtype.App id to s.(nstate.term) false])
                    <| nstate.lent := Some tv |>) with "Hphys") as "Hphys";
    [ by destruct s | ];
    iDestruct (own_raft_phys_unlend with "Hphys Htrk Hlog") as "Hphys";
    [ done | ];
    iDestruct (own_raft_phys_eq _ _ _ _
                 (send_msgs s [msg.mk mtype.App id to s.(nstate.term) false])
                 with "Hphys") as "Hphys";
    [ destruct s; simpl in Hlent; subst; done | ];
    iApply ("HΦ" $! true [msg.mk mtype.App id to s.(nstate.term) false]);
    iFrame "Hphys"; iPureIntro;
    rewrite /app_sends; apply Forall_cons_2; [ done | apply Forall_nil_2 ])).
  Qed.

End RaftMaybeSendAppendProof.
