Require Export New.proof.go_etcd_io.raft.election_proof.postulates_raft__maybeCommit.

Module RaftMaybeCommitProof (P : RAFT__MAYBECOMMIT_POSTULATES)
  : RAFT__MAYBECOMMIT.
Import P.

(** [ProgressTracker.Committed]'s quorum, stated over the voter set with
    [pvs_match_at] ([inv_tracker.v]), as the model's [acked_by] states it,
    over the [Match] map: a voter whose [Match] is at least a non-zero [N]
    has a [Progress], so it is in [prvals_match pvs]'s domain.  (At [N = 0]
    the two differ: [pvs_match_at] counts a voter with no [Progress] as
    [0].) *)
Lemma is_quorum_index_acked (cfg : gset w64)
    (pvs : gmap w64 (tracker.Progress.t * tracker.Inflights.t)) (N : w64) :
  (0 < uint.Z N)%Z →
  is_quorum_index cfg (pvs_match_at pvs) N →
  is_quorum cfg (dom (filter (λ '(_, x), uint.Z N ≤ uint.Z x) (prvals_match pvs))).
Proof.
  intros Hpos (_ & Hq & _). rewrite /is_quorum in Hq |- *.
  cut (size (filter (λ v, (uint.Z N ≤ uint.Z (pvs_match_at pvs v))%Z) cfg ∩ cfg)
       ≤ size (dom (filter (λ '(_, x), (uint.Z N ≤ uint.Z x)%Z) (prvals_match pvs)) ∩ cfg))%nat;
    [lia|].
  apply subseteq_size. intros v.
  rewrite !elem_of_intersection elem_of_filter elem_of_dom.
  intros [[Hle Hv] _]. split; [|done].
  rewrite /pvs_match_at /pvs_acked in Hle.
  destruct (pvs !! v) as [p|] eqn:E; simpl in Hle; [|word].
  exists p.1.(tracker.Progress.Match').
  apply map_lookup_filter_Some. split.
  - rewrite /prvals_match lookup_fmap E //.
  - simpl. lia.
Qed.

  (** The body, with its [defer]: [wp_with_defer] allocates the defer
      stack, the [traceCommit] closure is pushed onto it, and [return:]
      runs it ([wp_traceCommit]) before the function returns.

      [r.Term] is a field load; [r.trk.Committed()] runs on the tracker
      taken out with [own_raft_phys_tracker_same] (it gives the tracker
      back unchanged); [r.raftLog.maybeCommit] on the log taken out with
      [own_raft_phys_log_at] and put back at what it returns.  On [true],
      [raftLog.maybeCommit]'s condition gives the range and the term
      ([plog_matches] is [plog_term_at … = Some]), and [Committed]'s
      quorum index becomes [acked_by]'s quorum by
      [is_quorum_index_acked]: [N] is past [committed], so non-zero. *)
  Lemma wp_raft__maybeCommit : wp_raft__maybeCommit_body.
  Proof.
    intros_ambient.
    intros cfg r id s Hlead Hid.
    wp_start as "Hphys". iNamed "Hphys".
    wp_apply wp_with_defer as "%defer defer".
    simpl subst. wp_auto.
    wp_apply (wp_raft_load_Term with "Hphys") as "Hphys".
    iDestruct (own_raft_phys_tracker_same with "Hphys") as (tv) "(Htrkf & Htrk & Hback)".
    try wp_auto.
    wp_apply (wp_ProgressTracker__Committed with "[$Htrkf $Htrk]")
      as "%N (Htrkf & Htrk & %Hempty & %Hq)".
    iDestruct ("Hback" with "Htrkf Htrk") as "Hphys".
    try wp_auto.
    wp_apply (wp_raft_load_raftLog with "Hphys") as "Hphys".
    iDestruct (own_raft_phys_log_at with "Hphys") as "[Hlog Hlogback]".
    wp_apply (wp_raftLog__maybeCommit with "[$Hlog]") as "%b [Hlog %Hb]".
    iDestruct ("Hlogback" with "Hlog") as "Hphys".
    try wp_auto.
    wp_apply wp_traceCommit.
    try wp_auto.
    iApply ("HΦ" $! b N).
    destruct b.
    - iSplitL.
      { iApply (own_raft_phys_eq with "Hphys"). reflexivity. }
      iPureIntro. intros _.
      symmetry in Hb. apply bool_decide_eq_true_1 in Hb.
      destruct Hb as (_ & Hlt & Hm). cbn [raft.entryID.index' raft.entryID.term'] in *.
      rewrite /plog_matches /= in Hm.
      assert (Hne : cfg ≠ ∅) by set_solver.
      specialize (Hq Hne).
      rewrite /commit_ok /to_pstate /=.
      split_and!.
      + exact Hlt.
      + by apply plog_term_at_Some_range in Hm as [_ ?].
      + exact Hm.
      + rewrite /acked_by /= decide_True //.
        apply is_quorum_index_acked; [word | exact Hq].
    - iSplitL.
      { iApply (own_raft_phys_eq with "Hphys"). by destruct s as [?????????[]?]. }
      iPureIntro. done.
  Qed.

End RaftMaybeCommitProof.
