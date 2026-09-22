Require Export New.proof.go_etcd_io.raft.v3_proof.election.postulates_raft__maybeSendSnapshot.

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
      at the same [s], read back with [own_raft_phys_unsend].

      **Resources.**  The struct arrives as [own_raft_phys]; [pr] is
      borrowed out of its tracker with [own_tracker_lookup] (the premise
      puts it at [to] in [s.(nstate.progress)], which [Hprs] pins), and put
      back on every exit -- on the sending exit, before the [send], whose
      spec wants the struct whole. *)
  Lemma wp_raft__maybeSendSnapshot : wp_raft__maybeSendSnapshot_body.
  Proof.
    intros_ambient.
    intros cfg r id s to pr Hto Hprto Hlent.

    wp_start as "H". iNamed "H".
    iDestruct (is_pkg_init_access with "[$]") as "@".
    (** [is_pkg_init_access] hands the globals out *spatially*; the
        [raftLog.snapshot] call below consumes this one, and the
        [err == ErrSnapshotTemporarilyUnavailable] test afterwards needs it
        again, so move the (persistent) points-to into the □ context first. *)
    iDestruct "ErrSnapUnavail" as "#ErrSnapUnavail".
    iNamed "Hphys".
    iDestruct (own_raftLog_unless_open _ _ Hlent with "Hlog") as "Hlog".
    iDestruct (own_tracker_unless_open _ _ _ _ Hlent with "Htrk") as "Htrk".
    iDestruct (own_tracker_lookup _ _ _ _ _ _ Hprto with "Hprs Htrk")
      as "[Hpr Htrkback]".
    iNamed "Hpr".
    wp_auto.
    destruct pv.(tracker.Progress.RecentActive') eqn:Hra; wp_auto.
    2:{ (* not recently active: log and return [false] *)
      wp_apply wp_slice_literal. iSplitR; first done. iIntros "% [? _]".
      wp_auto. rewrite Hlok.
      wp_apply (wp_Logger__logf with "Hlogger").
      { solve_log_method. }
      iApply ("HΦ" $! false).
      iAssert (own_progress pr) with "[Hpv Hinfl]" as "Hpr".
      { rewrite /own_progress /own_progress_at. iExists pv, iv. iFrame "∗%". }
      iDestruct ("Htrkback" with "Hpr") as "Htrk".
      iDestruct (own_tracker_unless_close _ _ _ _ Hlent with "Htrk") as "Htrk".
      iDestruct (own_raftLog_unless_close _ _ Hlent with "Hlog") as "Hlog".
      iApply (own_raft_phys_intro with
        "Hr Hlogger Hprs Htrk Hlog Hmsgs Hmsgs_cap HmsgsAA HmsgsAA_cap Hmisc");
        done. }
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
      iAssert (own_progress pr) with "[Hpv Hinfl]" as "Hpr".
      { rewrite /own_progress /own_progress_at. iExists pv, iv. iFrame "∗%". }
      iDestruct ("Htrkback" with "Hpr") as "Htrk".
      iDestruct (own_tracker_unless_close _ _ _ _ Hlent with "Htrk") as "Htrk".
      iDestruct (own_raftLog_unless_close _ _ Hlent with "Hlog") as "Hlog".
      iApply (own_raft_phys_intro with
        "Hr Hlogger Hprs Htrk Hlog Hmsgs Hmsgs_cap HmsgsAA HmsgsAA_cap Hmisc");
        done.
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
      (* the [Progress] and the log go back before [send] *)
      iDestruct ("Htrkback" with "Hpr") as "Htrk".
      iDestruct (own_tracker_unless_close _ _ _ _ Hlent with "Htrk") as "Htrk".
      iDestruct (own_raftLog_unless_close _ _ Hlent with "Hlog") as "Hlog".
      iAssert (own_raft_phys cfg r id s)
        with "[Hr Htrk Hlog Hmsgs Hmsgs_cap HmsgsAA HmsgsAA_cap Hmisc]" as "Hphys".
      { iApply (own_raft_phys_intro with
          "Hr Hlogger Hprs Htrk Hlog Hmsgs Hmsgs_cap HmsgsAA HmsgsAA_cap Hmisc");
          done. }
      wp_apply (P.wp_raft__send with "[$Hphys]");
        [ done
        | right; right; split_and!;
          [ apply mtype_of_MsgSnap | w32_ne | w32_ne | done
          | intros Hc; exfalso; by apply Hto | done ]
        | ].
      iIntros "Hphys". wp_auto.
      iDestruct (own_raft_phys_unsend with "Hphys") as "Hphys".
      iApply ("HΦ" $! true). iFrame.
  Qed.

End RaftMaybeSendSnapshotProof.
