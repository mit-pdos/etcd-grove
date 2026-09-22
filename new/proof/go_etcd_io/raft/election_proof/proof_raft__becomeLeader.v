Require Export New.proof.go_etcd_io.raft.election_proof.postulates_raft__becomeLeader.

Module BecomeLeaderProof (P : BECOMELEADER_POSTULATES) : BECOMELEADER.
Import P.

  Lemma wp_raft__becomeLeader : wp_raft__becomeLeader_body.
  Proof.
    intros_ambient.
    intros cfg r id s.
    intros Hrole Hcfg. wp_start as "Hphys". iNamed "Hphys". wp_auto.
    (* [becomeLeader] panics on a follower; by assumption we are not one. *)
    assert (state_w64 s.(nstate.role) ≠ W64 0) as Hnf.
    { destruct (s.(nstate.role)) eqn:Hro; try congruence;
        rewrite /state_w64 /StateCandidate /StateLeader;
        intros Heq; apply (f_equal uint.Z) in Heq; vm_compute in Heq; discriminate. }
    rewrite Hstate bool_decide_eq_false_2 //. wp_auto.
    iAssert (own_raft_phys_at cfg r id s (functions raft.stepLeader []))
      with "[Hr Htrk Hlog Hmsgs Hmsgs_cap HmsgsAA HmsgsAA_cap Hmisc]"
      as "Hphys".
    { rewrite /own_raft_phys_at.
      iExists (rv <| raft.raft.step' := functions raft.stepLeader [] |>),
        msgs, msgsAA, lok. iFrame "Hr". simpl. iFrame "∗#%".
      iPureIntro. reflexivity. }
    (* [reset] is called at the unchanged term, so the vote survives *)
    rewrite Hterm.
    wp_apply (P.wp_raft__reset with "[$Hphys]") as "Hphys".
    iNamedSuffix "Hphys" "1".
    assert (rv0.(raft.raft.Vote') = s.(nstate.vote)) as Hvote1'.
    { rewrite Hvote1 /=. rewrite decide_True //. }
    (* [r.tick], [r.lead := r.id], [r.state := StateLeader] *)
    wp_auto.
    rewrite Hid1.
    (* the leader's own [Progress] is marked replicating and recently active *)
    wp_apply (wp_tracker_progress_lookup _ _ _ _ Hcfg with "[$Htrk1]")
      as "%pr [Hpr Hprback]".
    wp_apply (wp_Progress__BecomeReplicate with "[$Hpr]") as "Hpr".
    (* [own_progress] owns the whole [Progress] value (reshaped 2026-09-16 so
       that [reset]'s [Visit] closure can overwrite one wholesale), so the
       [RecentActive] assignment steps through [Hpv] with the generated
       [AccessStrict] instances and leaves [Inflights'] alone. *)
    (* [own_progress] became [∃ pv iv, own_progress_at pr pv iv] with four
       named conjuncts (2026-09-20); open it by name rather than
       positionally, and put it back through [own_progress_intro]. *)
    iDestruct "Hpr" as (pv iv) "Hpa". iNamed "Hpa".
    wp_auto.
    iAssert (own_progress pr) with "[Hpv Hinfl]" as "Hpr".
    { iApply (own_progress_intro _
                (pv <| tracker.Progress.RecentActive' := true |>) iv).
      rewrite /own_progress_at. iFrame "∗%". }
    iDestruct ("Hprback" with "Hpr") as "Htrk1".
    (* [lastIndex]'s spec is stated at a fixed split, so open
       [own_raftLog] and close it again. *)
    iDestruct (own_raftLog_acc with "Hlog1")
      as (lprev0 lsents0 luents0) "[Hlog1 Hlogback0]".
    wp_apply (wp_raftLog__lastIndex_at with "[$Hlog1]")
      as "%li [Hlog1 %Hli0]".
    iDestruct ("Hlogback0" with "Hlog1") as "Hlog1".
    wp_apply (wp_traceBecomeLeader with "[$Hmisc1]") as "Hmisc1".
    wp_apply wp_slice_literal. iSplitR; first done. iIntros "% [Hes _]".
    wp_auto.
    (* [appendEntry] queues a self-addressed [MsgAppResp], so it writes
       [r.msgsAfterAppend] and needs the whole struct -- not just the log, as
       its axiom used to claim.  [MsgAppResp] has no [mtype_of], so it drops
       out of the abstract outbox and the state is unchanged.  Re-seal for the
       call, then unpack again for the [Infof] that follows it. *)
    iAssert (own_raft_phys cfg r id (become_leader id s))
      with "[Hr1 Htrk1 Hlog1 Hmsgs1 Hmsgs_cap1 HmsgsAA1 HmsgsAA_cap1 Hmisc1]"
      as "Hphys".
    { rewrite /own_raft_phys /own_raft_phys_at /become_leader /step_func_of /=.
      iExists _, msgs0, msgsAA0, lok0.
      simpl in Hid1, Hterm1, Hvote1, Hlead1, Hstate1.
      iEval (simpl) in "Htrk1".
      iFrame "Hr1 ∗#%".
      iPureIntro. split_and!; done. }
    (* [appendEntry] writes [Term]/[Index] into every element of the slice,
       so it needs [Hes].  It returns [true] because the entry's [Data] is
       nil, which is what the premise says: with a zero payload
       [increaseUncommittedSize] cannot reject, so the [Panic] on the
       [false] branch below is dead code.  See [spec_raft__appendEntry.v]. *)
    wp_apply (wp_raft__appendEntry with "[$Hphys $Hes]") as "%ents' [Hphys Hes]".
    (* empty payload; [Type] is the zero value [EntryNormal], which is what
       keeps the log's [HnoConfChange] true; and one entry is not [2^61]. *)
    { apply Forall_singleton. done. }
    { apply Forall_singleton. done. }
    { rewrite length_insert /=. lia. }
    (* unpack again before [wp_auto]: the field reads in the [Infof] that
       follows cannot be stepped through the sealed predicate *)
    iNamedSuffix "Hphys" "2".
    wp_auto.
    wp_apply wp_slice_literal. iSplitR; first done. iIntros "% [? _]".
    wp_auto. rewrite Hlok2.
    wp_apply (wp_Logger__logf with "Hlogger2").
    { rewrite /log_methods. set_solver. }
    iApply "HΦ". rewrite /own_raft_phys /own_raft_phys_at.
    iExists _, _, _, _. iFrame "∗#%".
  Qed.

End BecomeLeaderProof.
