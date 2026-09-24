Require Export New.proof.go_etcd_io.raft.election_proof.postulates_raft__becomeLeader.

Module BecomeLeaderProof (P : BECOMELEADER_POSTULATES) : BECOMELEADER.
Import P.

  Lemma wp_raft__becomeLeader : wp_raft__becomeLeader_body.
  Proof.
    intros_ambient.
    intros cfg r id s.
    intros Hrole Hcfg Hlent. wp_start as "Hphys". wp_auto.
    (* [becomeLeader] panics on a follower; by assumption we are not one. *)
    assert (state_w64 s.(nstate.role) ≠ W64 0) as Hnf.
    { destruct (s.(nstate.role)) eqn:Hro; try congruence;
        rewrite /state_w64 /StateCandidate /StateLeader;
        intros Heq; apply (f_equal uint.Z) in Heq; vm_compute in Heq; discriminate. }
    wp_apply (wp_raft_load_state with "Hphys") as "Hphys".
    rewrite bool_decide_eq_false_2 //. wp_auto.
    (* [r.step := stepLeader], then [reset] at the unchanged term, so the vote
       survives *)
    (wp_apply (wp_raft_store_step with "Hphys") as "Hphys"; wp_apply (wp_raft_load_Term with "Hphys") as "Hphys").
    (* [reset]'s state is left to the frame: given explicitly, it has to be
       matched against [Hphys] up to conversion, which ran for 24 minutes
       before failing (2026-09-22) *)
    wp_apply (P.wp_raft__reset with "[$Hphys]"); first exact Hlent.
    iIntros "Hphys".
    (* [r.tick], [r.lead := r.id], [r.state := StateLeader] *)
    wp_auto. (wp_apply (wp_raft_store_tick with "Hphys") as "Hphys"; wp_apply (wp_raft_load_id with "Hphys") as "Hphys"; wp_apply (wp_raft_store_lead with "Hphys") as "Hphys"; wp_apply (wp_raft_store_state _ _ _ _ role.Leader with "Hphys") as "Hphys").
    (* the leader's own [Progress] is marked replicating and recently active;
       the map lookup is on the tracker object *)
    wp_apply (wp_raft_load_id with "Hphys") as "Hphys".
    iDestruct (own_raft_phys_tracker with "Hphys")
      as (tv) "(Htrkf & Htrk & Hback)"; first exact Hlent.
    wp_auto.
    wp_apply (wp_tracker_progress_lookup _ _ _ _ _ Hcfg with "[$Htrk]")
      as "%pr (_ & Hpr & Hprback)".
    iDestruct "Hpr" as (pv0 iv0) "Hpr".
    wp_apply (wp_Progress__BecomeReplicate with "[$Hpr]") as "Hpr".
    (* [own_progress] owns the whole [Progress] value (reshaped 2026-09-16 so
       that [reset]'s [Visit] closure can overwrite one wholesale), so the
       [RecentActive] assignment steps through [Hpv] with the generated
       [AccessStrict] instances and leaves [Inflights'] alone. *)
    iDestruct "Hpr" as (pv iv) "Hpa". iNamed "Hpa".
    wp_auto.
    iAssert (∃ pv iv, own_progress pr pv iv)%I with "[Hpv Hinfl]" as "Hpr".
    { iExists (pv <| tracker.Progress.RecentActive' := true |>), iv.
      rewrite /own_progress. iFrame "∗%". }
    iDestruct ("Hprback" with "Hpr") as "Htrk".
    iDestruct ("Hback" with "Htrkf Htrk") as "Hphys".
    (* [r.pendingConfIndex = r.raftLog.lastIndex()] *)
    wp_apply (wp_raft_load_raftLog with "Hphys") as "Hphys".
    iDestruct (own_raft_phys_log with "Hphys")
      as (ls Hls) "(Hlog & Hback)"; first exact Hlent.
    wp_apply (wp_raftLog__lastIndex _ _ Hls with "[$Hlog]") as "%li [Hlog _]".
    iDestruct ("Hback" with "Hlog [//]") as "Hphys".
    wp_apply (wp_raft_store_pendingConfIndex with "Hphys") as "Hphys".
    wp_apply wp_traceBecomeLeader. try wp_auto.
    wp_apply wp_slice_literal. iSplitR; first done. iIntros "% [Hes _]".
    wp_auto.
    (* the state is now [become_leader] up to the order of the record
       updates; no [simpl]: it carries a [functions …] value *)
    iDestruct (own_raft_phys_eq _ _ _ _ (become_leader id s) with "Hphys")
      as "Hphys".
    { by destruct s. }
    (* [appendEntry] writes [Term]/[Index] into every element of the slice,
       so it needs [Hes].  It returns [true] because the entry's [Data] is
       nil, which is what the premise says: with a zero payload
       [increaseUncommittedSize] cannot reject, so the [Panic] on the
       [false] branch below is dead code.  It also queues a self-addressed
       [MsgAppResp], which has no [mtype_of] and so drops out of the
       abstract outbox: the state is unchanged.  See
       [spec_raft__appendEntry.v]. *)
    wp_apply (wp_raft__appendEntry with "[$Hphys $Hes]") as "%ents' [Hphys Hes]".
    (* empty payload; [Type] is the zero value [EntryNormal], which is what
       keeps the log's [HnoConfChange] true; and one entry is not [2^61]. *)
    { apply Forall_singleton. done. }
    { apply Forall_singleton. done. }
    { rewrite length_insert /=. lia. }
    { exact Hlent. }
    (wp_apply (wp_raft_load_id with "Hphys") as "Hphys"; wp_apply (wp_raft_load_Term with "Hphys") as "Hphys"; wp_raft_log).
    iApply "HΦ". iFrame "Hphys".
  Qed.

End BecomeLeaderProof.
