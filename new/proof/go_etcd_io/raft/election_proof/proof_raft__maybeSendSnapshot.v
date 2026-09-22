Require Export New.proof.go_etcd_io.raft.election_proof.postulates_raft__maybeSendSnapshot.

Module RaftMaybeSendSnapshotProof (P : RAFT__MAYBESENDSNAPSHOT_POSTULATES)
  : RAFT__MAYBESENDSNAPSHOT.
Import P.

Section helpers.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : raft.Assumptions}.
Collection W := sem + package_sem.
Set Default Proof Using "W".

(** The outbox-only bookkeeping, as in [proof_raft__campaign.v] and
    [proof_raft__bcastAppend.v]; [Local] there and here.  Stated on
    [own_raft_bare] (2026-09-21) because that is what [send]'s postcondition
    hands back; note there is no [votes] premise, the vote tally having left
    with the tracker. *)
Local Lemma own_raft_bare_outbox (r : loc) (id : w64) f tv lg
    (s1 s2 : nstate.t) :
  s1.(nstate.term) = s2.(nstate.term) →
  s1.(nstate.vote) = s2.(nstate.vote) →
  s1.(nstate.lead) = s2.(nstate.lead) →
  s1.(nstate.role) = s2.(nstate.role) →
  s1.(nstate.outbox) ≡ₚ s2.(nstate.outbox) →
  own_raft_bare r id s1 f tv lg -∗ own_raft_bare r id s2 f tv lg.
Proof.
  intros H1 H2 H3 H4 H6. rewrite /own_raft_bare.
  iIntros "H". iNamed "H". iExists rv, msgs, msgsAA, lok.
  iFrame "Hr Hmsgs Hmsgs_cap HmsgsAA HmsgsAA_cap Hmisc Hlogger".
  iPureIntro. split_and!; first [ done | congruence | by rewrite -H6 ].
Qed.

(** A [send] the model does not see leaves the abstract state alone. *)
Local Lemma own_raft_bare_unsend (r : loc) (id : w64) f tv lg (s0 : nstate.t) :
  own_raft_bare r id (send_msgs s0 []) f tv lg -∗ own_raft_bare r id s0 f tv lg.
Proof.
  iIntros "H". iApply (own_raft_bare_outbox with "H"); try done.
  rewrite /send_msgs /= app_nil_r //.
Qed.

(** [MsgSnap] is not one of the four types the model describes, so
    [send_ok]'s third clause applies to it -- which is the whole reason the
    postcondition is at the same [s]. *)
Local Lemma mtype_of_MsgSnap : mtype_of MsgSnap = None.
Proof.
  rewrite /mtype_of.
  repeat (case_decide as Hc;
          [ exfalso; revert Hc; rewrite /MsgSnap /MsgVote /MsgVoteResp
              /MsgApp /MsgHeartbeat; intros Hc;
            apply (f_equal uint.Z) in Hc; vm_compute in Hc; discriminate
          | ]).
  done.
Qed.

End helpers.

Set Default Proof Using "Type".

  (** Three exits, and the two [panic]s are both killed by [is_Storage]'s
      [HSnapshot] ([inv_storage.v]), whose postcondition is the disjunction
      "[ErrSnapshotTemporarilyUnavailable], or a snapshot with
      [Metadata.Index ≠ 0]":

      - [!pr.RecentActive]: log, [false].  Nothing is touched.
      - [err = ErrSnapshotTemporarilyUnavailable]: log, [false].  This is
        where the [panic(err)] below would be, and the disjunction says the
        error is either this one or [nil].
      - otherwise the snapshot is non-empty, so [IsEmptySnap] answers
        [false] and the [panic("need non-empty snapshot")] is dead; the
        [MsgSnap] goes out and the answer is [true].

      **Comparing two non-[nil] errors is not free.**  [err ==
      ErrSnapshotTemporarilyUnavailable] does not reduce to a
      [bool_decide]: Goose's [go_eq_interface] first runs [CheckComparable]
      on the dynamic type, which has no reduction for an unknown type, so
      the proof is *stuck* until it knows the error's representation.  That
      is what [base.v]'s [is_new_error] clause on
      [ErrSnapshotTemporarilyUnavailable] supplies -- an interface holding a
      pointer, which is what [errors.New] builds.  [proof_raftLog__slice.v]
      compares against [ErrCompacted]/[ErrUnavailable] and does not need it
      only because there the error is [interface.nil], which the
      [nil]/[ok] case answers outright.

      The [send] is [send_ok]'s third clause: [mtype_of MsgSnap = None],
      [Term] is unset in the literal, and [To = to ≠ id] (the premise; the
      caller chain [bcastAppend] -> [maybeSendAppend] skips the leader
      itself).  So the abstract outbox is unchanged and the postcondition is
      at the same [s], read back with [own_raft_bare_unsend].

      **Resources** (reshaped 2026-09-21, see
      [spec_raft__maybeSendSnapshot.v]).  The struct arrives as
      [own_raft_notrk], i.e. [∃ lg, own_raft_bare … lg ∗ own_raftLog lg];
      [subst] immediately turns [f], [tv] and [lg] into fields of [rv], so
      what follows is the old script with [Htrk] deleted from every
      re-seal.  [send] wants the log out of the way too, so the one [send]
      is bracketed by an [own_raft_bare] assemble and an [iExists] that
      puts the log back. *)
  Lemma wp_raft__maybeSendSnapshot : wp_raft__maybeSendSnapshot_body.
  Proof.
    intros_ambient.
    intros r id s f tv to pr Hto.

    wp_start as "H". iNamed "H".
    iDestruct (is_pkg_init_access with "[$]") as "@".
    (** [is_pkg_init_access] hands the globals out *spatially*; the
        [raftLog.snapshot] call below consumes this one, and the
        [err == ErrSnapshotTemporarilyUnavailable] test afterwards needs it
        again, so move the (persistent) points-to into the □ context first. *)
    iDestruct "ErrSnapUnavail" as "#ErrSnapUnavail".
    iDestruct "Hphys" as (lg) "[Hbare Hlog]". iNamed "Hbare".
    subst f tv lg.
    iNamed "Hpr".
    wp_auto.
    destruct pv.(tracker.Progress.RecentActive') eqn:Hra; wp_auto.
    2:{ (* not recently active: log and return [false] *)
      wp_apply wp_slice_literal. iSplitR; first done. iIntros "% [? _]".
      wp_auto. rewrite Hlok.
      wp_apply (wp_Logger__logf with "Hlogger").
      { solve_log_method. }
      iApply ("HΦ" $! false).
      iSplitL "Hr Hlog Hmsgs Hmsgs_cap HmsgsAA HmsgsAA_cap Hmisc".
      { iApply (own_raft_notrk_intro with
          "Hlogger Hr Hlog Hmsgs Hmsgs_cap HmsgsAA HmsgsAA_cap Hmisc");
          done. }
      rewrite /own_progress /own_progress_at. iExists pv, iv. iFrame "∗%". }
    iDestruct (own_raftLog_acc with "Hlog") as (prev sents uents) "[Hlog Hlogback]".
    wp_apply (wp_raftLog__snapshot_at with "[$Hlog $ErrSnapUnavail]")
      as "%snap %err [Hlog %Herr]".
    iDestruct ("Hlogback" with "Hlog") as "Hlog".
    destruct Herr as [-> | [-> Hnz]].
    - (* [ErrSnapshotTemporarilyUnavailable]: log and return [false].  The
         [panic(err)] that follows the inner [if] is never reached. *)
      destruct HErrSnapUnavail_new as (t & p & ->).
      wp_auto. rewrite decide_True //. wp_auto.
      rewrite bool_decide_eq_true_2 //. wp_auto.
      wp_apply wp_slice_literal. iSplitR; first done. iIntros "% [? _]".
      wp_auto. rewrite Hlok.
      wp_apply (wp_Logger__logf with "Hlogger").
      { solve_log_method. }
      iApply ("HΦ" $! false).
      iSplitL "Hr Hlog Hmsgs Hmsgs_cap HmsgsAA HmsgsAA_cap Hmisc".
      { iApply (own_raft_notrk_intro with
          "Hlogger Hr Hlog Hmsgs Hmsgs_cap HmsgsAA HmsgsAA_cap Hmisc");
          done. }
      rewrite /own_progress /own_progress_at. iExists pv, iv. iFrame "∗%".
    - (* a real snapshot: [Metadata.Index ≠ 0] kills [IsEmptySnap]'s panic *)
      wp_auto.
      wp_apply wp_IsEmptySnap as "%b %Hb".
      rewrite Hb bool_decide_eq_false_2 //. wp_auto.
      (* the third [Debugf]'s argument list calls [firstIndex] and then
         reads [r.raftLog.committed] directly, so the log has to stay open
         across both *)
      iDestruct (own_raftLog_acc with "Hlog")
        as (prev2 sents2 uents2) "[Hlog Hlogback]".
      wp_apply (wp_raftLog__firstIndex_at with "[$Hlog]") as "%fi [Hlog %Hfi]".
      iNamed "Hlog".
      wp_auto.
      iAssert (own_raftLog rv.(raft.raft.raftLog'))
        with "[Hl HStorage Huents Huents_cap Hlogback]" as "Hlog".
      { iApply "Hlogback". rewrite /own_raftLog_at. iExists lv. iFrame "∗#%". }
      wp_apply wp_slice_literal. iSplitR; first done. iIntros "% [? _]".
      wp_auto. rewrite Hlok.
      wp_apply (wp_Logger__logf with "Hlogger").
      { solve_log_method. }
      iAssert (own_progress pr) with "[Hpv Hinfl]" as "Hpr".
      { rewrite /own_progress /own_progress_at. iExists pv, iv. iFrame "∗%". }
      wp_apply (wp_Progress__BecomeSnapshot with "[$Hpr]") as "Hpr".
      wp_apply wp_slice_literal. iSplitR; first done. iIntros "% [? _]".
      wp_auto. rewrite Hlok.
      wp_apply (wp_Logger__logf with "Hlogger").
      { solve_log_method. }
      iAssert (own_raft_bare r id s rv.(raft.raft.step') rv.(raft.raft.trk')
                 rv.(raft.raft.raftLog'))
        with "[Hr Hmsgs Hmsgs_cap HmsgsAA HmsgsAA_cap Hmisc]" as "Hbare".
      { iApply (own_raft_bare_intro with
          "Hlogger Hr Hmsgs Hmsgs_cap HmsgsAA HmsgsAA_cap Hmisc"); done. }
      wp_apply (P.wp_raft__send with "[$Hbare]");
        [ done
        | right; right; split_and!;
          [ apply mtype_of_MsgSnap | w32_ne | w32_ne | done
          | intros Hc; exfalso; by apply Hto | done ]
        | ].
      iIntros "Hbare". wp_auto.
      iDestruct (own_raft_bare_unsend with "Hbare") as "Hbare".
      iApply ("HΦ" $! true). iFrame "Hpr".
      rewrite /own_raft_notrk. iExists rv.(raft.raft.raftLog'). iFrame.
  Qed.

End RaftMaybeSendSnapshotProof.
