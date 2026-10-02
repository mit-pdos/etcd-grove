Require Export New.proof.go_etcd_io.raft.election_proof.postulates_ProgressTracker__TallyVotes.

Module ProgressTrackerTallyVotesProof (P : PROGRESSTRACKER__TALLYVOTES_POSTULATES) : PROGRESSTRACKER__TALLYVOTES.
Import P.

  Lemma wp_ProgressTracker__TallyVotes : wp_ProgressTracker__TallyVotes_body.
  Proof.
    intros_ambient.
    intros cfg trk tv [votes prs pvs] Hcfg_ne.

    wp_start as "(Htrk & Hown)". iNamed "Hown". trk_simpl.
    (* the [var _ quorum.VoteResult] declaration Go emits for the named return
       is an *anonymous* [GoAlloc], which [wp_auto] will not step past. *)
    wp_alloc res0 as "Hres0". wp_auto.
    set (Pgr := (λ k, votes !! k = Some true) : w64 → Prop).
    set (Prj := (λ k, votes !! k = Some false) : w64 → Prop).
    (* [pr] and [id] are the range's own loop variables: the body assigns them
       on every iteration, so they must be existentially quantified *inside*
       the invariant -- the same trap [proof_raft__campaign.v] documents for
       [slice.for_range]. *)
    set (Pmap := (λ (keys : list w64) (i : Z),
      ∃ (prv : loc) (idv : w64),
        "%Hi" ∷ ⌜ 0 ≤ i ⌝ ∗
        "Htrk" ∷ trk ↦ tv ∗
        "Hvotes" ∷ tv.(tracker.ProgressTracker.Votes') ↦$ votes ∗
        "Hprogs" ∷ ([∗ map] pr; p ∈ prs; pvs, own_Progress pr p) ∗
        "p" ∷ p_ptr ↦ trk ∗
        "pr" ∷ pr_ptr ↦ prv ∗
        "id" ∷ id_ptr ↦ idv ∗
        "granted" ∷ granted_ptr ↦ W64 (nsat Pgr (take (Z.to_nat i) keys)) ∗
        "rejected" ∷ rejected_ptr ↦ W64 (nsat Prj (take (Z.to_nat i) keys)))%I).
    wp_apply (wp_map_for_range Pmap with "Hprs").
    iIntros (keys) "(%Hkset & %Hklen & %Hknodup)".
    iSplitL "Htrk Hvotes Hprogs p pr id granted rejected".
    { rewrite /Pmap. iExists null, (W64 0).
      rewrite take_0 /nsat filter_nil /=. iFrame. iPureIntro. lia. }
    iSplitL "".
    { iIntros "!>" (i key prl) "[%Hkey %Hprl] HP". rewrite /Pmap. iNamed "HP".
      iDestruct (big_sepM2_lookup_iff with "Hprogs") as %Hiff.
      destruct (proj1 (Hiff key) ltac:(by eexists)) as [pk Hpvk].
      iDestruct (big_sepM2_lookup_acc _ _ _ _ _ _ Hprl Hpvk with "Hprogs")
        as "[Hpr Hback]".
      iNamed "Hpr".
      pose proof Habs as Habs'. apply progress_abs_Some in Habs' as (Hnolearner & _).
      assert (Z.to_nat (i + 1) = S (Z.to_nat i)) as Hsucc.
      { rewrite -Z2Nat.inj_succ; last lia. f_equal. all: lia. }
      assert (take (Z.to_nat (i + 1)) keys = take (Z.to_nat i) keys ++ [key])
        as Htake.
      { rewrite Hsucc. by apply take_S_r. }
      assert (size prs = size cfg) as Hszprs by (rewrite -Hprs_dom size_dom //).
      (* the counters are bounded by [size cfg], which is what lets [word] see
         that [granted + 1] does not wrap *)
      assert (nsat Pgr (take (Z.to_nat i) keys) ≤ size cfg)%nat as HgB.
      { etrans; first apply nsat_le. rewrite length_take Hklen Hszprs. lia. }
      assert (nsat Prj (take (Z.to_nat i) keys) ≤ size cfg)%nat as HrB.
      { etrans; first apply nsat_le. rewrite length_take Hklen Hszprs. lia. }
      wp_auto.
      (* [if pr.IsLearner { continue }]: no voter is a learner, and without
         [Hnolearner] the [if] scrutinee is not a literal and [wp_auto] parks. *)
      rewrite Hnolearner. wp_auto.
      wp_apply (wp_map_lookup2 with "Hvotes"). iIntros "Hvotes".
      iDestruct ("Hback" with "[Hpv Hinfl]") as "Hprogs".
      { iExists _. iFrame "Hpv Hinfl". done. }
      destruct (votes !! key) as [[|]|] eqn:Hvk.
      - (* granted *)
        assert (Pgr key) as HPg by (rewrite /Pgr Hvk //).
        assert (¬ Prj key) as HPr by (rewrite /Prj Hvk; congruence).
        rewrite bool_decide_eq_true_2; last by eexists.
        wp_auto.
        iRight. iLeft. iSplit; first done.
        iExists prl, key. rewrite Htake !nsat_snoc.
        destruct (decide (Pgr key)); last done.
        destruct (decide (Prj key)); first done.
        rewrite Nat.add_0_r.
        replace (W64 (nsat Pgr (take (Z.to_nat i) keys) + 1)%nat)
          with (word.add (W64 (nsat Pgr (take (Z.to_nat i) keys))) (W64 1))
          by word.
        iFrame. iPureIntro. lia.
      - (* rejected *)
        assert (¬ Pgr key) as HPg by (rewrite /Pgr Hvk; congruence).
        assert (Prj key) as HPr by (rewrite /Prj Hvk //).
        rewrite bool_decide_eq_true_2; last by eexists.
        wp_auto.
        iRight. iLeft. iSplit; first done.
        iExists prl, key. rewrite Htake !nsat_snoc.
        destruct (decide (Pgr key)); first done.
        destruct (decide (Prj key)); last done.
        rewrite Nat.add_0_r.
        replace (W64 (nsat Prj (take (Z.to_nat i) keys) + 1)%nat)
          with (word.add (W64 (nsat Prj (take (Z.to_nat i) keys))) (W64 1))
          by word.
        iFrame. iPureIntro. lia.
      - (* this voter has not answered: [continue], both counters unchanged *)
        assert (¬ Pgr key) as HPg by (rewrite /Pgr Hvk; congruence).
        assert (¬ Prj key) as HPr by (rewrite /Prj Hvk; congruence).
        rewrite bool_decide_eq_false_2; last by intros [? ?].
        wp_auto.
        iLeft. iSplit; first done.
        iExists prl, key. rewrite Htake !nsat_snoc.
        destruct (decide (Pgr key)); first done.
        destruct (decide (Prj key)); first done.
        rewrite !Nat.add_0_r.
        iFrame. iPureIntro. lia. }
    (* the range is over, so the counters hold the whole tally *)
    iIntros "HP _". rewrite /Pmap. iNamed "HP".
    rewrite Nat2Z.id -Hklen firstn_all.
    assert ((list_to_set keys : gset w64) = cfg) as Hkcfg
      by (rewrite Hkset Hprs_dom //).
    assert (nsat Pgr keys = size (granted votes ∩ cfg)) as Hgfin.
    { rewrite /Pgr. by apply nsat_granted. }
    assert (nsat Prj keys = size (rejected votes ∩ cfg)) as Hrfin.
    { rewrite /Prj. by apply nsat_rejected. }
    wp_auto.
    (* [p.Config.Voters.VoteResult(p.Votes)]: re-seal the tracker and ask the
       joint quorum.  The two counters already hold the model's numbers. *)
    wp_apply (wp_JointConfig__VoteResult _ _ _ (trk.mk votes prs pvs) Hcfg_ne with
               "[$Htrk Hvotes Hprogs Hvoters Hlearners HlearnersNext]").
    { rewrite /own_tracker.
      iExists voters_ref, voters, learners, learnersNext. iFrame "∗#%". }
    iIntros (res) "(Htrk & Hown & %Hres & %Hwon & %Hlost)".
    wp_auto.
    iApply ("HΦ" $! (W64 (nsat Pgr keys)) (W64 (nsat Prj keys)) res).
    iFrame "Htrk Hown".
    iPureIntro. split_and!.
    - done.
    - intros Heq. by apply Hwon.
    - intros Heq. by apply Hlost.
  Qed.

End ProgressTrackerTallyVotesProof.
