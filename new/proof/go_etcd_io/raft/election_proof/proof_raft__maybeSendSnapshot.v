Require Export New.proof.go_etcd_io.raft.election_proof.postulates_raft__maybeSendSnapshot.

Module RaftMaybeSendSnapshotProof (P : RAFT__MAYBESENDSNAPSHOT_POSTULATES)
  : RAFT__MAYBESENDSNAPSHOT.
Import P.

Section helpers.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : raft.Assumptions}.
Collection W := sem + package_sem.
Set Default Proof Using "W".

(** Returning without sending: the state the caller expects. *)
Local Lemma own_raft_phys_nosend cfg r id s :
  own_raft_phys cfg r id (s <| nstate.prvals := s.(nstate.prvals) |>) -∗
  own_raft_phys cfg r id (send_msgs s [] <| nstate.prvals := s.(nstate.prvals) |>).
Proof.
  iIntros "H". iApply (own_raft_phys_eq with "H").
  rewrite /send_msgs app_nil_r. by destruct s.
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

      **Resources.**  The struct arrives as [own_raft_phys], and stays
      whole except around the two accesses to [*pr]: the
      [pr.RecentActive] load and [pr.BecomeSnapshot].  Each borrows [pr]
      out of the tracker by its key ([own_tracker_lookup]; the premise
      puts it at [to] in [s.(nstate.progress)]) and gives it back at once
      -- the first at the same value, the second at whatever
      [BecomeSnapshot] leaves, which the postcondition's [pvs] records.
      In between, the log lines read raft fields and the [raftLog] calls
      take the log out with [own_raft_phys_log_same].  (Until 2026-09-29
      the tracker was lent out of the struct for the whole body,
      [nstate.lent].) *)
  Lemma wp_raft__maybeSendSnapshot : wp_raft__maybeSendSnapshot_body.
  Proof.
    intros_ambient.
    intros cfg r id s to pr Hto Hprto.

    wp_start as "H". iNamed "H".
    iDestruct (is_pkg_init_access with "[$]") as "@".
    (** [is_pkg_init_access] hands the globals out *spatially*; the
        [raftLog.snapshot] call below consumes this one, and the
        [err == ErrSnapshotTemporarilyUnavailable] test afterwards needs it
        again, so move the (persistent) points-to into the □ context first. *)
    iDestruct "ErrSnapUnavail" as "#ErrSnapUnavail".
    (* [pr.RecentActive]: borrow [pr] for the load, and give it back *)
    iDestruct (own_raft_phys_tracker_same with "Hphys") as (tv) "(Htrkf & Htrk & Hback)".
    iDestruct (own_tracker_lookup_same _ _ _ _ _ _ _ Hprto with "Htrk")
      as (pv iv Hpv) "[Hpr Htrkback]".
    iNamed "Hpr".
    wp_auto.
    iAssert (own_progress pr pv iv) with "[Hpv Hinfl]" as "Hpr".
    { rewrite /own_progress. iFrame "∗%". }
    iDestruct ("Htrkback" with "Hpr") as "Htrk".
    iDestruct ("Hback" with "Htrkf Htrk") as "Hphys".
    (* nothing below writes a [Progress] until [BecomeSnapshot] *)
    iAssert (own_raft_phys cfg r id (s <| nstate.prvals := s.(nstate.prvals) |>))%I
      with "[Hphys]" as "Hphys".
    { iApply (own_raft_phys_eq with "Hphys"). by destruct s. }
    destruct pv.(tracker.Progress.RecentActive') eqn:Hra; wp_auto.
    2:{ (* not recently active: log and return [false] *)
      wp_raft_log.
      iApply ("HΦ" $! false [] s.(nstate.prvals)).
      iDestruct (own_raft_phys_nosend with "Hphys") as "$".
      iPureIntro. split; [constructor|done]. }
    wp_apply (wp_raft_load_raftLog with "Hphys") as "Hphys".
    iDestruct (own_raft_phys_log_same with "Hphys") as "[Hlog Hlogback]".
    wp_apply (wp_raftLog__snapshot _ _ _ with "[$Hlog $ErrSnapUnavail]")
      as "%snap %err [Hlog %Herr]".
    iDestruct ("Hlogback" with "Hlog") as "Hphys".
    destruct Herr as [-> | [-> Hnz]].
    - (* [ErrSnapshotTemporarilyUnavailable]: log and return [false].  The
         [panic(err)] that follows the inner [if] is never reached. *)
      destruct HErrSnapUnavail_new as (t & p & ->).
      wp_auto. rewrite decide_True //. wp_auto.
      rewrite bool_decide_eq_true_2 //. wp_auto.
      (wp_apply (wp_raft_load_id with "Hphys") as "Hphys"; wp_raft_log).
      iApply ("HΦ" $! false [] s.(nstate.prvals)).
      iDestruct (own_raft_phys_nosend with "Hphys") as "$".
      iPureIntro. split; [constructor|done].
    - (* a real snapshot: [Metadata.Index ≠ 0] kills [IsEmptySnap]'s panic *)
      wp_auto.
      wp_apply wp_IsEmptySnap as "%b %Hb".
      rewrite Hb bool_decide_eq_false_2 //. wp_auto.
      (* the third [Debugf]'s argument list calls [firstIndex] and then
         reads [r.raftLog.committed] directly: the log's struct, for the
         read *)
      wp_apply (wp_raft_load_id with "Hphys") as "Hphys".
      wp_apply (wp_raft_load_raftLog with "Hphys") as "Hphys".
      iDestruct (own_raft_phys_log_same with "Hphys") as "[Hlog Hlogback]".
      wp_apply (wp_raftLog__firstIndex _ _ with "[$Hlog]") as "%fi [Hlog %Hfi]".
      iDestruct ("Hlogback" with "Hlog") as "Hphys".
      wp_apply (wp_raft_load_raftLog with "Hphys") as "Hphys".
      iDestruct (own_raft_phys_log_same with "Hphys") as "[Hlog Hlogback]".
      iDestruct (own_raftLog_struct with "Hlog") as (lv) "(Hl & _ & Hlb)".
      wp_auto.
      iDestruct ("Hlb" with "Hl") as "Hlog".
      iDestruct ("Hlogback" with "Hlog") as "Hphys".
      wp_raft_log.
      (* [pr.BecomeSnapshot(sindex)]: borrow [pr] again, give it back at
         the new value *)
      iDestruct (own_raft_phys_tracker_prvals with "Hphys")
        as (tv1) "(Htrkf & Htrk & Hback)".
      iDestruct (own_tracker_lookup _ _ _ _ _ _ _ Hprto with "Htrk")
        as (pv1 iv1 Hpv1) "[Hpr Htrkback]".
      wp_apply (wp_Progress__BecomeSnapshot with "[$Hpr]") as "Hpr".
      iDestruct "Hpr" as (pv2 iv2) "[Hpr %Hm2]".
      iDestruct ("Htrkback" with "Hpr") as "Htrk".
      iDestruct ("Hback" with "Htrkf Htrk") as "Hphys".
      (wp_apply (wp_raft_load_id with "Hphys") as "Hphys"; wp_raft_log).
      (* [send_ok]'s stamped clause, for [MsgSnap], with no entries *)
      wp_apply (P.wp_raft__send _ _ _ _ _ []
                  [msg.mk mtype.Snap id to s.(nstate.term) false
                     (W64 0) (W64 0) (W64 0) (W64 0) []] with "[$Hphys]").
      { done. }
      { right; left; exists mtype.Snap; split_and!;
          [ right; right; left; done | apply mtype_of_MsgSnap | done | exact Hto
          | reflexivity ]. }
      { iApply own_slice_nil. }
      iIntros "Hphys". wp_auto.
      iApply ("HΦ" $! true _ (<[to := (pv2, iv2)]> s.(nstate.prvals))).
      iSplitL.
      { iApply (own_raft_phys_eq with "Hphys"). by destruct s. }
      iPureIntro. split.
      + rewrite /repl_sends. apply Forall_singleton. right.
        rewrite /snap_ok /=. split_and!; done.
      + by apply (prvals_match_insert_same _ _ (pv1, iv1)).
  Qed.

End RaftMaybeSendSnapshotProof.
