Require Export New.proof.go_etcd_io.raft.v3_proof.election.postulates_raft__maybeSendAppend.

Module RaftMaybeSendAppendProof (P : RAFT__MAYBESENDAPPEND_POSTULATES)
  : RAFT__MAYBESENDAPPEND.
Import P.

Section helpers.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : raft.Assumptions}.
Collection W := sem + package_sem.
Set Default Proof Using "W".

Context (cfg : gset w64).

(** The outbox-only bookkeeping, as in [proof_raft__campaign.v]; [Local]
    there and here. *)
Local Lemma own_raft_phys_outbox (r : loc) (id : w64) (s1 s2 : nstate.t) :
  s1.(nstate.term) = s2.(nstate.term) →
  s1.(nstate.vote) = s2.(nstate.vote) →
  s1.(nstate.lead) = s2.(nstate.lead) →
  s1.(nstate.role) = s2.(nstate.role) →
  s1.(nstate.votes) = s2.(nstate.votes) →
  s1.(nstate.outbox) ≡ₚ s2.(nstate.outbox) →
  own_raft_phys cfg r id s1 -∗ own_raft_phys cfg r id s2.
Proof.
  intros H1 H2 H3 H4 H5 H6. rewrite /own_raft_phys.
  iIntros "H". iNamed "H". iExists rv, msgs, msgsAA, lok.
  rewrite -H5.
  iFrame "Hr Htrk Hlog Hmsgs Hmsgs_cap HmsgsAA HmsgsAA_cap Hmisc Hlogger".
  iPureIntro. split_and!; first [ done | congruence | by rewrite -H6 ].
Qed.

(** Three of the four exits send nothing, and the postcondition is stated at
    [send_msgs s ms]; this is [ms = []]. *)
Local Lemma own_raft_phys_send_nil (r : loc) (id : w64) (s0 : nstate.t) :
  own_raft_phys cfg r id s0 -∗ own_raft_phys cfg r id (send_msgs s0 []).
Proof.
  iIntros "H". iApply (own_raft_phys_outbox with "H"); try done.
  rewrite /send_msgs /= app_nil_r //.
Qed.

(** [own_raftLog_at]'s no-wrap bound, read out without consuming the log.
    Same lemma as [proof_raftLog__entries.v]'s, and [Local] for the same
    reason. *)
Local Lemma raftLog_at_nowrap l prev sents uents :
  own_raftLog_at l prev sents uents -∗
  ⌜ (uint.Z prev.(raft.entryID.index') + Z.of_nat (length sents)
     + Z.of_nat (length uents) + 1 < 2^64)%Z ⌝ ∗
  own_raftLog_at l prev sents uents.
Proof.
  iIntros "H". iDestruct "H" as (lv) "H". iNamed "H".
  iAssert (own_raftLog_at l prev sents uents) with "[-]" as "Hlog".
  { rewrite /own_raftLog_at. iExists lv. iFrame "∗#%". }
  iSplitR "Hlog"; [ iPureIntro; exact Hnowrap | iExact "Hlog" ].
Qed.

(** Lend out just the [raftLog] record.  Needed on the branch where
    [raftLog.entries] is *not* called and the log is therefore still whole:
    the message literal reads [r.raftLog.committed], and the three branches
    have to reach that read holding the same resources. *)
Local Lemma own_raftLog_at_open l prev sents uents :
  own_raftLog_at l prev sents uents -∗
  ∃ (lv : raft.raftLog.t),
    l ↦ lv ∗ (l ↦ lv -∗ own_raftLog_at l prev sents uents).
Proof.
  iIntros "H". iDestruct "H" as (lv) "H". iNamed "H".
  iExists lv. iFrame "Hl". iIntros "Hl".
  rewrite /own_raftLog_at. iExists lv. iFrame "∗#%".
Qed.

(** ** What the three arms of [pr.State != StateReplicate || !pr.Inflights.Full()]
       have in common

    The [if] has three outcomes -- not in [StateReplicate]; in it with room
    in the window; in it with the window full -- and the first two run
    [r.raftLog.entries] while the third leaves [ents] at the zero slice.
    Everything after the [if] is the same program, so the three are brought
    to a common state and the rest of the proof is written once (the three
    goals are discharged by one [;]-chained script below).

    The four existentials are the page: where it is, what is in it, at what
    fraction, and the [raftLog] record it was carved out of.  On the third
    arm they are [slice.nil], [[]], [DfracOwn 1] and the log's own record --
    [own_slice_nil] supplies the (empty) page, and rebinding the zero slice
    to a variable is what makes that arm's *program text* match the other
    two's, which is what lets one script serve all three.

    [Hlb] is the accessor that takes the page (and the record) back; see
    [spec_raftLog__entries.v] for why both travel together.  [Hwin] is
    [Progress.SentEntries]'s second premise in the only form all three arms
    can supply it: entries are fetched only when the window has room, so a
    non-empty page in [StateReplicate] means the window was not full -- and
    nothing between the test and [SentEntries] touches the window. *)
Definition msa_pkg (ep lgp : loc) (pv : tracker.Progress.t)
    (iv : tracker.Inflights.t) (prev : raft.entryID.t)
    (sents uents : list raftpb.Entry.t) : iProp Σ :=
  ∃ (sl : slice.t) (es : list raftpb.Entry.t) (dq : dfrac)
    (lv : raft.raftLog.t),
  "ents" ∷ ep ↦ sl ∗
  "Hl" ∷ lgp ↦ lv ∗
  "Hpage" ∷ sl ↦*{dq} es ∗
  "Hlb" ∷ (lgp ↦ lv -∗ sl ↦*{dq} es -∗ own_raftLog_at lgp prev sents uents) ∗
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

  (** [r.maybeSendAppend(to, sendIfEmpty)]
      ([raft__maybeSendAppendⁱᵐᵖˡ], new/code/go_etcd_io/raft/v3.v:3096).

      **The two specs this proof needs were repaired first** (2026-09-21,
      notes/false-statements.md).  Both defects were the same one: a
      predicate that hides the struct under [∃ rv] cannot say "this call
      does not touch field [f]", and this function holds *two* pointers read
      out of the struct across [r.send(...)].

      - one voter's [Progress], borrowed out of [own_tracker].  [send] and
        [maybeSendSnapshot] are now stated on [own_raft_bare] /
        [own_raft_notrk] ([inv_raft_phys.v]), which pin the tracker value as
        a parameter and do not own the tracker, so the borrow survives the
        call and [pr.SentEntries]/[pr.SentCommit] can be called on the same
        pointer with no second lookup.  On the old statements
        [maybeSendSnapshot]'s precondition was outright *contradictory*
        here, the [Progress] being inside the [own_raft_phys] it also asked
        for.
      - one page of entries, borrowed out of [own_raftLog] by
        [raftLog.entries].  The page and the whole log cannot be held at
        once -- the page aliases the log -- and the page is needed *after*
        the send, by [payloadsSize].  So [send] does not ask for the log
        either ([own_raft_bare] pins the log pointer and owns nothing behind
        it), and [raftLog.entries] hands the [raftLog] *record* back
        alongside the page, which is what makes the literal's
        [Commit: r.raftLog.committed] steppable while the page is out.

      The script, following the body:

      - [pr := r.trk.Progress[to]] hits because [to ∈ cfg]: take the
        (persistent) progress map out with [own_tracker_progress_map], step
        the lookup with [wp_map_lookup1], and borrow the [own_progress] with
        [own_tracker_lookup].  The borrow is returned exactly once, at
        whichever exit is taken.
      - [pr.IsPaused()]: on [true], return [false] having sent nothing; on
        [false] the answer [progress_paused pv = false] gives
        [pv.State ≠ StateSnapshot], which is [SentEntries]'s first premise.
      - [r.raftLog.term(pr.Next-1)] through [own_raftLog_acc].  On an error
        (the [interface.ok] case), [maybeSendSnapshot], whose postcondition
        is at the same abstract state -- [MsgSnap] is model-invisible.  On
        [interface.nil], the iff of [spec_raftLog__term.v] gives
        [prev.index ≤ pr.Next - 1], and with [own_raftLog_at]'s [Hnowrap]
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
    intros cfg r id s to sendIfEmpty Hto Hcfg.
    wp_start_folded as "Hphys".
    (* the tracker and the log come out of the struct before the body is in
       the goal; both are lent out below and [send] must not ask for either *)
    iDestruct (own_raft_bare_split with "Hphys") as (tv lg) "(Hbare & Htrk & Hlog)".
    iNamed "Hbare". subst tv lg.
    iDestruct (own_tracker_progress_map with "Htrk") as (prs) "(#Hprs & %Hdom & Htrk)".
    assert (is_Some (prs !! to)) as [pr Hlk].
    { apply elem_of_dom. rewrite Hdom //. }
    iDestruct (own_tracker_lookup _ _ _ _ _ _ Hlk with "Hprs Htrk") as "[Hpr Hprback]".
    wp_start_unfold.
    wp_auto.
    wp_apply (wp_map_lookup1 with "Hprs") as "_".
    rewrite Hlk /=.
    iDestruct "Hpr" as (pv iv) "Hpa".
    wp_apply (wp_Progress__IsPaused with "[$Hpa]") as "Hpa".
    destruct (progress_paused pv) eqn:Hpaused.
    { (* paused: nothing is sent, [false] *)
      wp_auto.
      iDestruct (own_progress_intro with "Hpa") as "Hpr".
      iDestruct ("Hprback" with "Hpr") as "Htrk".
      iAssert (own_raft_phys cfg r id s)
        with "[Hr Htrk Hlog Hmsgs Hmsgs_cap HmsgsAA HmsgsAA_cap Hmisc]" as "Hphys".
      { iApply (own_raft_phys_intro with
          "Hlogger Hr Htrk Hlog Hmsgs Hmsgs_cap HmsgsAA HmsgsAA_cap Hmisc"); done. }
      iDestruct (own_raft_phys_send_nil with "Hphys") as "Hphys".
      iApply ("HΦ" $! false []). iFrame "Hphys". iPureIntro. constructor. }
    (* not paused, so not in [StateSnapshot] -- [SentEntries]' first premise *)
    assert (Hnosnap : pv.(tracker.Progress.State') ≠ W64 2).
    { intros Hc. rewrite /progress_paused decide_True // in Hpaused. }
    iNamed "Hpa".
    wp_auto.
    (* [r.raftLog.term(pr.Next - 1)] *)
    iDestruct (own_raftLog_acc with "Hlog") as (prev sents uents) "[Hlog Hlogback]".
    iDestruct (raftLog_at_nowrap with "Hlog") as "[%Hnw Hlog]".
    wp_apply (wp_raftLog__term_at with "[$Hlog]") as "%pterm %err [Hlog %Herr]".
    destruct err as [eok|].
    { (* the log no longer has [pr.Next - 1]: fall back to a snapshot.
         [wp_pure] first: [wp_auto] alone will not step the
         [Convert go.untyped_bool] in front of the [err != nil] test. *)
      wp_pure. wp_auto.
      iDestruct ("Hlogback" with "Hlog") as "Hlog".
      iAssert (own_progress pr) with "[Hpv Hinfl]" as "Hpr".
      { rewrite /own_progress /own_progress_at. iExists pv, iv. iFrame "∗%". }
      iAssert (own_raft_notrk r id s (step_func_of s.(nstate.role))
                 rv.(raft.raft.trk'))
        with "[Hr Hlog Hmsgs Hmsgs_cap HmsgsAA HmsgsAA_cap Hmisc]" as "Hphys".
      { iApply (own_raft_notrk_intro with
          "Hlogger Hr Hlog Hmsgs Hmsgs_cap HmsgsAA HmsgsAA_cap Hmisc"); done. }
      wp_apply (P.wp_raft__maybeSendSnapshot _ _ _ _ _ _ _ Hto with "[$Hphys $Hpr]")
        as "%b [Hphys Hpr]".
      try wp_auto.
      iDestruct ("Hprback" with "Hpr") as "Htrk".
      iDestruct (own_raft_notrk_join with "Hphys Htrk") as "Hphys".
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
      wp_apply (wp_Inflights__Full with "[$Hinfl]") as "Hinfl";
      destruct (inflights_full iv) eqn:Hfull;
      [ (* in [StateReplicate] with the window full: no entries are fetched,
           and the log stays whole -- open it just far enough to read
           [committed] later *)
        iDestruct (own_raftLog_at_open with "Hlog") as (lvo) "[Hl Hlb0]";
        iAssert (msa_pkg ents_ptr rv.(raft.raft.raftLog') pv iv prev sents uents)
          with "[ents Hl Hlb0]" as "HC";
        [ rewrite /msa_pkg; iExists slice.nil, [], (DfracOwn 1), lvo;
          iFrame "ents Hl";
          iSplitR; [ iApply own_slice_nil | ];
          iSplitL "Hlb0"; [ iIntros "Hl _"; iApply "Hlb0"; iFrame | ];
          iPureIntro; intros _ Hne; exfalso; exact (Hne eq_refl)
        | ]
      | (* in [StateReplicate] with room: fetch a page *)
        wp_auto;
        wp_apply (wp_raftLog__entries_at _ _ _ _ _ _ Hlo with "[$Hlog]")
          as "%sl_e %es_e %dq_e %lv_e (Hl & Hpage & Hlogback2)";
        try wp_auto;
        iAssert (msa_pkg ents_ptr rv.(raft.raft.raftLog') pv iv prev sents uents)
          with "[ents Hl Hpage Hlogback2]" as "HC";
        [ rewrite /msa_pkg; iExists sl_e, es_e, dq_e, lv_e; iFrame;
          iPureIntro; intros _ _; exact Hfull | ] ]
    | (* not in [StateReplicate]: the first disjunct is true, fetch a page *)
      rewrite bool_decide_eq_false_2 //; wp_auto;
      wp_apply (wp_raftLog__entries_at _ _ _ _ _ _ Hlo with "[$Hlog]")
        as "%sl_e %es_e %dq_e %lv_e (Hl & Hpage & Hlogback2)";
      try wp_auto;
      iAssert (msa_pkg ents_ptr rv.(raft.raft.raftLog') pv iv prev sents uents)
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
        iDestruct ("Hlb" with "Hl Hpage") as "Hlog";
        iDestruct ("Hlogback" with "Hlog") as "Hlog";
        iAssert (own_progress pr) with "[Hpv Hinfl]" as "Hpr";
        [ rewrite /own_progress /own_progress_at; iExists pv, iv; iFrame "∗%" | ];
        iDestruct ("Hprback" with "Hpr") as "Htrk";
        iAssert (own_raft_phys cfg r id s)
          with "[Hr Htrk Hlog Hmsgs Hmsgs_cap HmsgsAA HmsgsAA_cap Hmisc]" as "Hphys";
        [ iApply (own_raft_phys_intro with
            "Hlogger Hr Htrk Hlog Hmsgs Hmsgs_cap HmsgsAA HmsgsAA_cap Hmisc");
          done | ];
        iDestruct (own_raft_phys_send_nil with "Hphys") as "Hphys";
        iApply ("HΦ" $! false []); iFrame "Hphys"; iPureIntro;
        rewrite /app_sends; apply Forall_nil_2 ]
    | wp_auto ];
    (* --- the message goes out; again once per goal --- *)
    (* the literal reads [r.raftLog.committed] through [Hl] *)
    (try wp_auto;
    iAssert (own_raft_bare r id s (step_func_of s.(nstate.role))
               rv.(raft.raft.trk') rv.(raft.raft.raftLog'))
      with "[Hr Hmsgs Hmsgs_cap HmsgsAA HmsgsAA_cap Hmisc]" as "Hbare";
    [ iApply (own_raft_bare_intro with
        "Hlogger Hr Hmsgs Hmsgs_cap HmsgsAA HmsgsAA_cap Hmisc"); done | ];
    wp_apply (P.wp_raft__send with "[$Hbare]");
      [ done
      | right; left; exists mtype.App; split_and!;
        [ by left | apply mtype_of_MsgApp | done | exact Hto | done ]
      | ];
    iIntros "Hbare";
    (* [send] hands the struct back at the same [trk] and [raftLog], which is
       why [Hl] and the [Progress] borrow are still usable *)
    iDestruct "Hbare" as (rv2 msgs2 msgsAA2 lok2) "Hb"; iNamedSuffix "Hb" "2";
    iEval (rewrite -Hlg2) in "Hl";
    try wp_auto;
    wp_apply (wp_payloadsSize with "[$Hpage]") as "%psz [Hpage _]";
    iAssert (own_progress_at pr pv iv) with "[Hpv Hinfl]" as "Hpa";
    [ rewrite /own_progress_at; iFrame "∗%" | ];
    assert (Hwin2 : pv.(tracker.Progress.State') = W64 1 →
                    (0 < sint.Z sl.(slice.len))%Z → inflights_full iv = false);
    [ intros H1 H2; apply Hwin; [exact H1|]; intros Heq; rewrite Heq in Hlen;
      simpl in Hlen; lia | ];
    wp_apply (wp_Progress__SentEntries _ _ _ _ _ Hnosnap Hwin2 with "[$Hpa]")
      as "Hpr";
    try wp_auto;
    iDestruct "Hpr" as (pv3 iv3) "Hpa3";
    wp_apply (wp_Progress__SentCommit with "[$Hpa3]") as "Hpa3";
    try wp_auto;
    iEval (rewrite Hlg2) in "Hl";
    iDestruct ("Hlb" with "Hl Hpage") as "Hlog";
    iDestruct ("Hlogback" with "Hlog") as "Hlog";
    iDestruct (own_progress_intro with "Hpa3") as "Hpr";
    iDestruct ("Hprback" with "Hpr") as "Htrk";
    iAssert (own_raft_bare r id
               (send_msgs s [msg.mk mtype.App id to s.(nstate.term) false])
               (step_func_of s.(nstate.role)) rv.(raft.raft.trk')
               rv.(raft.raft.raftLog'))
      with "[Hr2 Hmsgs2 Hmsgs_cap2 HmsgsAA2 HmsgsAA_cap2 Hmisc2]" as "Hbare";
    [ iApply (own_raft_bare_intro with
        "Hlogger2 Hr2 Hmsgs2 Hmsgs_cap2 HmsgsAA2 HmsgsAA_cap2 Hmisc2"); done | ];
    iDestruct (own_raft_bare_join with "Hbare Htrk Hlog") as "Hphys";
    iApply ("HΦ" $! true [msg.mk mtype.App id to s.(nstate.term) false]);
    iFrame "Hphys"; iPureIntro;
    rewrite /app_sends; apply Forall_cons_2; [ done | apply Forall_nil_2 ])).
  Qed.

End RaftMaybeSendAppendProof.
