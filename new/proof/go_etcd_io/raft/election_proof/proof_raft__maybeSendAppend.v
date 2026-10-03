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

(** ** What the three arms of [pr.State != StateReplicate || !pr.Inflights.Full()]
       have in common

    The [if] has three outcomes -- not in [StateReplicate]; in it with room
    in the window; in it with the window full -- and the first two run
    [r.raftLog.entries] while the third leaves [ents] at the zero slice.
    Everything after the [if] is the same program, so the three are brought
    to a common state and the rest of the proof is written once (the three
    goals are discharged by one [;]-chained script below).

    The existentials are [ents]: the slice and its entries, read-only
    ([raftLog.entries] hands them out for good), so the log in the struct
    is unchanged.  The struct is whole and at [s]: [pr] went back after the
    reads each arm makes, at the same value.  On the third arm the
    existentials are [slice.nil] and [[]], and rebinding the zero slice to
    a variable is what makes that arm's *program text* match the other
    two's, which is what lets one script serve all three.  [Hwin] is
    [Progress.SentEntries]'s second premise in the only form all three arms
    can supply it: entries are fetched only when the window has room, so a
    non-empty [ents] in [StateReplicate] means the window was not full --
    and nothing between the test and [SentEntries] touches the window,
    which [nstate.prvals] records. *)
Definition msa_pkg (r : loc) (id : w64) (s : nstate.t) (ep : loc)
    (p : progress.t) : iProp Σ :=
  ∃ (sl : slice.t) (es : list raftpb.Entry.t),
  "ents" ∷ ep ↦ sl ∗
  "Hents" ∷ sl ↦*□ es ∗
  "Hphys" ∷ own_raft_phys cfg r id s ∗
  "%Hwin" ∷ ⌜ p.(progress.state) = prstate.Replicate → es ≠ [] →
              inflights_full p.(progress.infl) = false ⌝ ∗
  "%Hpkgin" ∷ ⌜ Forall (λ e, e ∈ (to_pstate s).(pstate.log)) es ⌝ ∗
  "%Hpkgpre" ∷ ⌜ es `prefix_of` plog_from (to_pstate s).(pstate.base) (to_pstate s).(pstate.log)
                                 p.(progress.next) ⌝.

(** The [MsgApp]'s batch, from what the log says ([app_ok]'s last two
    clauses): [Index = pr.Next - 1], the entries a prefix of the log from
    [pr.Next]. *)
Lemma msa_app_facts (s : nstate.t) prev sents uents lcm lap snap (t n : w64) es :
  s.(nstate.logst) = logstate.mk prev sents uents lcm lap snap →
  plog_wf prev (sents ++ uents) →
  (uint.Z prev.(raft.entryID.index') + Z.of_nat (length sents)
   + Z.of_nat (length uents) + 1 < 2^64)%Z →
  (uint.Z prev.(raft.entryID.index') ≤ uint.Z (word.sub n (W64 1)) ≤
   uint.Z prev.(raft.entryID.index') + Z.of_nat (length sents) + Z.of_nat (length uents))%Z →
  Forall (λ e, e.(raftpb.Entry.Type') = W32 0) (sents ++ uents) →
  es `prefix_of` plog_from (to_pstate s).(pstate.base) (to_pstate s).(pstate.log) n →
  es `prefix_of` plog_from (to_pstate s).(pstate.base) (to_pstate s).(pstate.log)
                   (word.add (word.sub n (W64 1)) (W64 1)) ∧
  (plog_wf (raft.entryID.mk t (word.sub n (W64 1))) es ∧
   uint.Z (word.sub n (W64 1)) + Z.of_nat (length es) + 1 < 2 ^ 64 ∧
   Forall (λ e, e.(raftpb.Entry.Type') = W32 0) es).
Proof.
  intros Hls Hwf Hnw Hi HN Hpre.
  rewrite (_ : word.add (word.sub n (W64 1)) (W64 1) = n); [|word].
  split; [exact Hpre|].
  rewrite /to_pstate Hls /= in Hpre.
  apply (app_payload_from_log prev (sents ++ uents)); try done.
  - rewrite length_app. lia.
  - rewrite /plog_last_index_Z length_app. lia.
  - rewrite (_ : word.add (word.sub n (W64 1)) (W64 1) = n); [exact Hpre|word].
Qed.


End helpers.

Set Default Proof Using "Type".

  (* Open the log's record for a read of [r.raftLog.committed], which the
     next [wp_auto] steps; [close_struct] puts it back at the same state. *)
  Local Ltac open_struct :=
    iDestruct (own_raft_phys_log_same with "Hphys") as "[Hlog Hlogback]";
    iDestruct (own_raftLog_struct with "Hlog") as (?) "(Hl & _ & Hlb)".
  (* The same, keeping what was read: [Commit] in the [MsgApp] literal *)
  Local Ltac open_struct_c :=
    iDestruct (own_raft_phys_log_same with "Hphys") as "[Hlog Hlogback]";
    iDestruct (own_raftLog_struct with "Hlog") as (lvc) "(Hl & %Hlvc & Hlb)".
  Local Ltac close_struct :=
    iDestruct ("Hlb" with "Hl") as "Hlog";
    iDestruct ("Hlogback" with "Hlog") as "Hphys".

  (** [r.maybeSendAppend(to, sendIfEmpty)]
      ([raft__maybeSendAppendⁱᵐᵖˡ], new/code/go_etcd_io/raft/v3.v:3096).

      **What is held across [r.send(...)].**  One voter's [Progress] --
      [pr.SentEntries] needs what this proof learned about it before the
      send (not [StateSnapshot]; a non-full window in [StateReplicate]) --
      and [ents], which [raftLog.entries] hands out read-only and for good
      ([payloadsSize] reads it after the send).  Neither is lent: [pr] is
      borrowed out of the struct for each stretch of the body that touches
      it ([own_raft_phys_pr] and its variants) and given back
      before the next access to the struct, and what the proof knows about
      it survives the calls in between because the state records its value
      ([nstate.prvals], [s.(nstate.prvals) !! to = Some p]) and
      [send] changes only the outbox.  (Until 2026-09-29 the tracker was
      lent out of the struct for the whole body, [nstate.lent].)  Each
      [raftLog] call and each read of [r.raftLog.committed] takes the log
      out with [own_raft_phys_log_same] and puts it back.

      [maybeSendSnapshot] borrows the [Progress] again by its key in
      [s.(nstate.progress)].

      The script, following the body:

      - [pr := r.trk.Progress[to]] hits because [to ∈ cfg]: take the
        (persistent) progress map out with [own_tracker_progress_map], step
        the lookup with [wp_map_lookup1]; [own_tracker_prvals_dom] gives
        [pr]'s record [p].
      - [pr.IsPaused()]: on [true], return [false] having sent nothing; on
        [false] the answer [progress_is_paused p = false] gives
        [p.state ≠ Snapshot], which is [SentEntries]'s first premise.
      - [r.raftLog.term(pr.Next-1)] at the log's state.  On an error
        (the [interface.ok] case), [maybeSendSnapshot], whose postcondition
        is a [repl_sends] list ([MsgSnap]s) with [Match] untouched.  On [interface.nil], the iff of
        [spec_raftLog__term.v] gives [prev.index ≤ pr.Next - 1], and with
        [own_raftLog_core]'s [Hnowrap] that is [prev.index + 1 ≤ pr.Next]:
        [pr.Next = 0] is excluded because then the argument is [2^64 - 1],
        which the range puts out of bounds.  That inequality is
        [raftLog.entries]'s only premise.
      - the [||] and its three arms: see [msa_pkg] above.
      - [len(ents) == 0 && !sendIfEmpty] returns [false].
      - the second [if err != nil] is dead: [err] is [interface.nil] from
        the [term] call, and [raftLog.entries] returns [interface.nil] too.
      - [r.send(pb.Message{To: to, Type: MsgApp, ...})] with [send_ok]'s
        second clause: [Term] is unset in the literal, [To = to ≠ id], and
        [out] is the abstraction of the [MsgApp] literal, which is
        [app_ok]: [Commit] is [r.raftLog.committed] ([own_raftLog_struct]),
        the entries are entries of the log ([msa_pkg]'s [Hpkgin]).
      - [SentEntries(len ents, payloadsSize ents)] and
        [SentCommit(r.raftLog.committed)], then [return true]; the
        postcondition's [pvs] is what they leave. *)
  Lemma wp_raft__maybeSendAppend : wp_raft__maybeSendAppend_body.
  Proof.
    intros_ambient.
    intros cfg r id s to sendIfEmpty Hto Hcfg.
    wp_start_folded as "Hphys".
    (* the log's state, as variables *)
    destruct (s.(nstate.logst)) as [prev sents uents lcm lap snap] eqn:Hls.
    (* the [iNamed] only strips the precondition's name *)
    iNamed "Hphys".
    (* [r.trk.Progress] is read through the tracker field *)
    iDestruct (own_raft_phys_tracker_same with "Hphys") as (tv) "(Htrkf & Htrk & Hback)".
    iDestruct (own_tracker_progress_map with "Htrk") as "(#Hprs & %Hdom & Htrk)".
    iDestruct (own_tracker_prvals_dom with "Htrk") as "[%Hpdom Htrk]".
    assert (is_Some (s.(nstate.progress) !! to)) as [pr Hlk].
    { apply elem_of_dom. rewrite Hdom //. }
    assert (is_Some (s.(nstate.prvals) !! to)) as [p Hpvs].
    { apply elem_of_dom. rewrite Hpdom elem_of_dom. by eexists. }
    wp_start_unfold.
    wp_auto.
    iDestruct ("Hback" with "Htrkf Htrk") as "Hphys".
    wp_apply (wp_map_lookup1 with "Hprs") as "_".
    rewrite Hlk /=.
    (* [pr.IsPaused()] and [prevIndex := pr.Next - 1], on [pr] borrowed *)
    iDestruct (own_raft_phys_pr with "Hphys [//] [//]") as "[Hpa Hpback]".
    wp_apply (wp_Progress__IsPaused with "[$Hpa]") as "Hpa".
    destruct (progress_is_paused p) eqn:Hpaused.
    { (* paused: nothing is sent, [false] *)
      wp_auto.
      iDestruct ("Hpback" with "Hpa") as "Hphys".
      iDestruct (own_raft_phys_send_nil with "Hphys") as "Hphys".
      iApply ("HΦ" $! false [] s.(nstate.prvals)). iSplitL.
      - iApply (own_raft_phys_eq with "Hphys"). by destruct s.
      - iPureIntro. split; [constructor|done]. }
    (* not paused, so not in [StateSnapshot] -- [SentEntries]' first premise *)
    assert (Hnosnap : p.(progress.state) ≠ prstate.Snapshot).
    { intros Hc. rewrite /progress_is_paused Hc /= in Hpaused. discriminate. }
    (* [pr.Next], read off the value: the record's [next] *)
    iNamed "Hpa".
    pose proof Habs as Habs0.
    apply progress_abs_Some in Habs0 as (_ & Hst & _ & Hnx & _).
    wp_auto. rewrite Hnx.
    iDestruct ("Hpback" with "[Hpv Hinfl]") as "Hphys".
    { iExists _. iFrame "∗%". }
    wp_apply (wp_raft_load_raftLog with "Hphys") as "Hphys".
    (* [r.raftLog.term(pr.Next - 1)] *)
    iDestruct (own_raft_phys_log_same with "Hphys") as "[Hlog Hlogback]".
    iEval (rewrite Hls) in "Hlog".
    iDestruct (own_raftLog_nowrap with "Hlog") as "[%Hnw Hlog]".
    cbn [logstate.prev logstate.sents logstate.uents] in Hnw.
    iDestruct (own_raftLog_wf with "Hlog") as "[%Hlwf Hlog]".
    iDestruct (own_raftLog_no_confchange with "Hlog") as "[%Hlnc Hlog]".
    cbn [logstate.prev logstate.sents logstate.uents] in Hlwf, Hlnc.
    wp_apply (wp_raftLog__term _ (logstate.mk prev sents uents lcm lap snap) _ with "[$Hlog]")
      as "%pterm %err (Hlog & %Herr & %Hterm_at & _)".
    cbn [logstate.prev logstate.sents logstate.uents] in Herr.
    iEval (rewrite -Hls) in "Hlog".
    iDestruct ("Hlogback" with "Hlog") as "Hphys".
    destruct err as [eok|].
    { (* the log no longer has [pr.Next - 1]: fall back to a snapshot.
         [wp_pure] first: [wp_auto] alone will not step the
         [Convert go.untyped_bool] in front of the [err != nil] test. *)
      wp_pure. wp_auto.
      wp_apply (P.wp_raft__maybeSendSnapshot _ _ _ _ _ _ Hto Hlk
                  with "[$Hphys]") as "%b %ms' %pvs' (Hphys & %Hms' & %Hmm')".
      try wp_auto.
      iApply ("HΦ" $! b ms' pvs'). iFrame "Hphys". done. }
    (* [err = nil]: the iff gives [pr.Next] a lower bound against the log *)
    destruct Herr as [Herr1 _]. specialize (Herr1 eq_refl).
    (* and the term it returned is the log's at [pr.Next - 1]: [app_ok]'s
       [logterm] clause *)
    specialize (Hterm_at eq_refl).
    assert (Hlo : (uint.Z prev.(raft.entryID.index') + 1
                   ≤ uint.Z p.(progress.next))%Z) by word.
    wp_pure.
    (* [pr.State], [pr.Inflights.Full()], [pr.Next]: borrow [pr] again *)
    iDestruct (own_raft_phys_pr with "Hphys [//] [//]") as "[Hpa Hpback]".
    clear Hst Hnx Habs. iNamed "Hpa".
    pose proof Habs as Habs0.
    apply progress_abs_Some in Habs0 as (_ & Hst & _ & Hnx & _).
    wp_auto. rewrite Hst ?Hnx.
    (* the three arms of the [||], each ending at [msa_pkg] *)
    destruct (decide (p.(progress.state) = prstate.Replicate)) as [Hrep|Hnrep];
    [ rewrite bool_decide_eq_true_2; last (rewrite Hrep; done); wp_auto;
      wp_apply (wp_Inflights__Full with "[$Hinfl]") as "Hinfl";
      destruct (inflights_full p.(progress.infl)) eqn:Hfull;
      [ (* in [StateReplicate] with the window full: no entries are fetched *)
        iDestruct ("Hpback" with "[Hpv Hinfl]") as "Hphys";
        [ iExists _; iFrame "∗%" | ];
        iAssert (msa_pkg cfg r id s ents_ptr p)
          with "[ents Hphys]" as "HC";
        [ rewrite /msa_pkg; iExists slice.nil, [];
          iFrame "ents Hphys";
          iSplitR; [ iApply own_slice_nil | ];
          iPureIntro; split_and!; [ intros _ Hne; exfalso; exact (Hne eq_refl) | apply Forall_nil_2 | apply prefix_nil ]
        | ]
      | (* in [StateReplicate] with room: fetch [ents] *)
        wp_auto;
        iDestruct ("Hpback" with "[Hpv Hinfl]") as "Hphys";
        [ iExists _; iFrame "∗%" | ];
        wp_apply (wp_raft_load_maxMsgSize with "Hphys") as "%mms Hphys";
        wp_apply (wp_raft_load_raftLog with "Hphys") as "Hphys";
        iDestruct (own_raft_phys_log_same with "Hphys") as "[Hlog Hlogback]";
        iEval (rewrite Hls) in "Hlog";
        rewrite ?Hnx;
        wp_apply (wp_raftLog__entries _ (logstate.mk prev sents uents lcm lap snap) _ _ Hlo with "[$Hlog]")
          as "%sl_e %es_e (Hlog & Hents & [%Hin %Hpre])";
        iEval (rewrite -Hls) in "Hlog";
        iDestruct ("Hlogback" with "Hlog") as "Hphys";
        try wp_auto;
        iAssert (msa_pkg cfg r id s ents_ptr p)
          with "[ents Hphys Hents]" as "HC";
        [ rewrite /msa_pkg; iExists sl_e, es_e; iFrame "ents Hents Hphys";
          iPureIntro; split_and!;
          [ intros _ _; exact Hfull
          | apply List.Forall_forall; intros e He; rewrite /= Hls; apply Hin; by apply list_elem_of_In
          | rewrite /= Hls; exact Hpre ]
        | ] ]
    | (* not in [StateReplicate]: the first disjunct is true, fetch [ents] *)
      rewrite bool_decide_eq_false_2;
        last (intros Hc; apply Hnrep, prstate_w64_inj; exact Hc); wp_auto;
      iDestruct ("Hpback" with "[Hpv Hinfl]") as "Hphys";
      [ iExists _; iFrame "∗%" | ];
      wp_apply (wp_raft_load_maxMsgSize with "Hphys") as "%mms Hphys";
      wp_apply (wp_raft_load_raftLog with "Hphys") as "Hphys";
      iDestruct (own_raft_phys_log_same with "Hphys") as "[Hlog Hlogback]";
      iEval (rewrite Hls) in "Hlog";
      rewrite ?Hnx;
      wp_apply (wp_raftLog__entries _ (logstate.mk prev sents uents lcm lap snap) _ _ Hlo with "[$Hlog]")
        as "%sl_e %es_e (Hlog & Hents & [%Hin %Hpre])";
      iEval (rewrite -Hls) in "Hlog";
      iDestruct ("Hlogback" with "Hlog") as "Hphys";
      try wp_auto;
      iAssert (msa_pkg cfg r id s ents_ptr p)
        with "[ents Hphys Hents]" as "HC";
      [ rewrite /msa_pkg; iExists sl_e, es_e; iFrame "ents Hents Hphys";
        iPureIntro; split_and!;
        [ intros Hc; contradiction
        | apply List.Forall_forall; intros e He; rewrite /= Hls; apply Hin; by apply list_elem_of_In
        | rewrite /= Hls; exact Hpre ]
      | ] ];
    (* --- three goals from here on, in the same state; the rest of the
           proof is one tactic, parenthesised so that it runs once per goal
           (in Ltac1 [A; [b|c]] counts *all* open goals, not the ones the
           previous step made) --- *)
    (iEval (rewrite /msa_pkg) in "HC"; iNamed "HC"; iDestruct "Hents" as "#Hents"; try wp_auto;
    iDestruct (slice_len_Z with "Hents") as %Hlen;
    (* [if len(ents) == 0 && !sendIfEmpty { return false }] *)
    case_bool_decide as Hc1;
    [ wp_auto; destruct sendIfEmpty;
      [ wp_auto
      | (* no entries, and the caller does not want an empty append *)
        wp_auto;
        iDestruct (own_raft_phys_send_nil with "Hphys") as "Hphys";
        iApply ("HΦ" $! false [] s.(nstate.prvals)); iSplitL;
        [ iApply (own_raft_phys_eq with "Hphys"); by destruct s
        | iPureIntro; split; [ apply Forall_nil_2 | done ] ] ]
    | wp_auto ];
    (* --- the message goes out; again once per goal --- *)
    (* the literal reads [r.raftLog.committed] through the log's record *)
    (try wp_auto; wp_apply (wp_raft_load_raftLog with "Hphys") as "Hphys";
    open_struct_c; try wp_auto; close_struct;
    wp_apply (P.wp_raft__send _ _ _ _ _ es with "[$Hphys]");
      [ done
      | right; left; exists mtype.App; split_and!;
        [ by left | apply mtype_of_MsgApp | done | exact Hto | done ]
      | iSplitR; [iApply "Hents" | iApply send_no_snap; simpl; w32_ne]
      | ];
    iIntros "Hphys";
    try wp_auto;
    wp_apply (wp_payloadsSize with "[$Hents]") as "%psz [_ _]";
    (* [pr.SentEntries(...)]: [send] changed only the outbox, so [pr] is
       still at [p] *)
    iDestruct (own_raft_phys_pr_upd with "Hphys [//] [//]") as "[Hpa Hpback]";
    assert (Hwin2 : p.(progress.state) = prstate.Replicate →
                    (0 < sint.Z sl.(slice.len))%Z → inflights_full p.(progress.infl) = false);
    [ intros H1 H2; apply Hwin; [exact H1|]; intros Heq; rewrite Heq in Hlen;
      simpl in Hlen; lia | ];
    wp_apply (wp_Progress__SentEntries _ _ _ _ Hnosnap Hwin2 with "[$Hpa]")
      as "Hpr";
    iDestruct ("Hpback" with "Hpr") as "Hphys";
    (* [pr.SentCommit(r.raftLog.committed)]: the argument first, then [pr]
       once more, at the value [SentEntries] left *)
    try wp_auto; wp_apply (wp_raft_load_raftLog with "Hphys") as "Hphys";
    open_struct; try wp_auto; close_struct;
    iDestruct (own_raft_phys_pr_upd _ _ _ _ _ _ (progress_sent_entries p sl.(slice.len) psz)
                 with "Hphys [//] []")
      as "[Hpa3 Hpback]";
    [ iPureIntro; rewrite /= lookup_insert_eq //
    | ];
    wp_apply (wp_Progress__SentCommit with "[$Hpa3]") as "Hpa4";
    iDestruct ("Hpback" with "Hpa4") as "Hphys";
    try wp_auto;
    pose proof (msa_app_facts s prev sents uents lcm lap snap pterm p.(progress.next) es
                  Hls Hlwf Hnw Herr1 Hlnc Hpkgpre) as Hfacts;
    iApply ("HΦ" $! true);
    iSplitL;
    [ iApply (own_raft_phys_eq with "Hphys"); reflexivity
    | iPureIntro; split;
      [ rewrite /repl_sends; apply Forall_singleton; left;
        rewrite /app_ok /=; split_and!;
        [ done | done | done | exact Hto
        | rewrite Hls; exact Hterm_at
        | destruct Hlvc as [Hlvc _]; rewrite Hlvc Hls /=; lia
        | exact Hpkgin
        | exact (proj1 Hfacts)
        | exact (proj2 Hfacts) ]
      | rewrite /= insert_insert_eq;
        apply (prvals_match_insert_same _ _ p); [ exact Hpvs | ];
        rewrite /progress_sent_commit /progress_sent_entries /=;
        destruct (p.(progress.state)); repeat case_decide; done ] ])).
  Qed.

End RaftMaybeSendAppendProof.
