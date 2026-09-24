Require Export New.proof.go_etcd_io.raft.election_proof.postulates_raft__maybeSendSnapshot.

Module RaftMaybeSendSnapshotProof (P : RAFT__MAYBESENDSNAPSHOT_POSTULATES)
  : RAFT__MAYBESENDSNAPSHOT.
Import P.

Section helpers.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : raft.Assumptions}.
Collection W := sem + package_sem.
Set Default Proof Using "W".

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

  (* End the loan, and get from the state [own_raft_phys_unlend] names back
     to [s]. *)
  Local Ltac finish s Hlent :=
    iDestruct (own_raft_phys_unlend with "Hphys Htrk Hlog") as "Hphys";
    [ done | ];
    iDestruct (own_raft_phys_eq _ _ _ _ s with "Hphys") as "Hphys";
    [ destruct s; simpl in Hlent; subst; done | ].

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

      **Resources.**  The struct arrives as [own_raft_phys].  The body
      holds [pr] -- borrowed out of the tracker with [own_tracker_lookup]
      (the premise puts it at [to] in [s.(nstate.progress)]) -- and the log
      at the same time as it reads raft fields for its log lines, so the
      tracker and the log are lent out of the struct ([own_raft_phys_lend])
      and the loan ends on every exit ([finish]) -- on the sending exit,
      before the [send], whose spec wants the struct whole. *)
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
    iDestruct (own_raft_phys_lend _ _ _ _ Hlent with "Hphys")
      as (tv ls Hls) "(Htrk & Hlog & Hphys)".
    iDestruct (own_tracker_lookup _ _ _ _ _ _ Hprto with "Htrk")
      as "[Hpr Htrkback]".
    iNamed "Hpr".
    wp_auto.
    destruct pv.(tracker.Progress.RecentActive') eqn:Hra; wp_auto.
    2:{ (* not recently active: log and return [false] *)
      wp_raft_log.
      iApply ("HΦ" $! false).
      iAssert (∃ pv iv, own_progress pr pv iv)%I with "[Hpv Hinfl]" as "Hpr".
      { iExists pv, iv. rewrite /own_progress. iFrame "∗%". }
      iDestruct ("Htrkback" with "Hpr") as "Htrk".
      finish s Hlent. iFrame "Hphys". }
    wp_apply (wp_raft_load_raftLog with "Hphys") as "Hphys".
    wp_apply (wp_raftLog__snapshot _ _ _ Hls with "[$Hlog $ErrSnapUnavail]")
      as "%snap %err [Hlog %Herr]".
    destruct Herr as [-> | [-> Hnz]].
    - (* [ErrSnapshotTemporarilyUnavailable]: log and return [false].  The
         [panic(err)] that follows the inner [if] is never reached. *)
      destruct HErrSnapUnavail_new as (t & p & ->).
      wp_auto. rewrite decide_True //. wp_auto.
      rewrite bool_decide_eq_true_2 //. wp_auto.
      (wp_apply (wp_raft_load_id with "Hphys") as "Hphys"; wp_raft_log).
      iApply ("HΦ" $! false).
      iAssert (∃ pv iv, own_progress pr pv iv)%I with "[Hpv Hinfl]" as "Hpr".
      { iExists pv, iv. rewrite /own_progress. iFrame "∗%". }
      iDestruct ("Htrkback" with "Hpr") as "Htrk".
      finish s Hlent. iFrame "Hphys".
    - (* a real snapshot: [Metadata.Index ≠ 0] kills [IsEmptySnap]'s panic *)
      wp_auto.
      wp_apply wp_IsEmptySnap as "%b %Hb".
      rewrite Hb bool_decide_eq_false_2 //. wp_auto.
      (* the third [Debugf]'s argument list calls [firstIndex] and then
         reads [r.raftLog.committed] directly: the log's struct, for the
         read *)
      wp_apply (wp_raft_load_id with "Hphys") as "Hphys".
      wp_apply (wp_raft_load_raftLog with "Hphys") as "Hphys".
      wp_apply (wp_raftLog__firstIndex _ _ Hls with "[$Hlog]") as "%fi [Hlog %Hfi]".
      wp_apply (wp_raft_load_raftLog with "Hphys") as "Hphys".
      iDestruct (own_raftLog_struct with "Hlog") as (lv) "(Hl & _ & Hlogback)".
      wp_auto.
      iDestruct ("Hlogback" with "Hl") as "Hlog".
      wp_raft_log.
      iAssert (own_progress pr pv iv) with "[Hpv Hinfl]" as "Hpr".
      { rewrite /own_progress. iFrame "∗%". }
      wp_apply (wp_Progress__BecomeSnapshot with "[$Hpr]") as "Hpr".
      (wp_apply (wp_raft_load_id with "Hphys") as "Hphys"; wp_raft_log).
      (* the [Progress] and the log go back before [send] *)
      iDestruct ("Htrkback" with "Hpr") as "Htrk".
      finish s Hlent.
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
