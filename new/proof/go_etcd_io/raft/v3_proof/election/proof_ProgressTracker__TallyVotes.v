Require Export New.proof.go_etcd_io.raft.v3_proof.election.postulates_ProgressTracker__TallyVotes.

Module ProgressTrackerTallyVotesProof (P : PROGRESSTRACKER__TALLYVOTES_POSTULATES) : PROGRESSTRACKER__TALLYVOTES.

  Lemma wp_ProgressTracker__TallyVotes : wp_ProgressTracker__TallyVotes_body.
  Proof.
    intros_ambient.
    intros cfg trk tv votes.

    (* Everything down to the [Admitted] is machine-checked. *)
    wp_start as "(Htrk & Hown)". iNamed "Hown".
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
        "Hprogs" ∷ ([∗ map] pr ∈ prs, own_progress pr) ∗
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
      iDestruct (big_sepM_lookup_acc _ _ _ _ Hprl with "Hprogs") as "[Hpr Hback]".
      iNamed "Hpr".
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
      { rewrite /own_progress. iExists _. iFrame. done. }
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
    iIntros "HP". rewrite /Pmap. iNamed "HP".
    rewrite Nat2Z.id -Hklen firstn_all.
    assert ((list_to_set keys : gset w64) = cfg) as Hkcfg
      by (rewrite Hkset Hprs_dom //).
    assert (nsat Pgr keys = size (granted votes ∩ cfg)) as Hgfin.
    { rewrite /Pgr. by apply nsat_granted. }
    assert (nsat Prj keys = size (rejected votes ∩ cfg)) as Hrfin.
    { rewrite /Prj. by apply nsat_rejected. }
    wp_auto.
    (* STUCK, and this is the real stuck point.  The remaining program is

         let: "$r0" := ((trk.[ProgressTracker.t,"Config"]).[Config.t,"Voters"])
                         @! (go.PointerType quorum.JointConfig) @! "VoteResult"
                           (# tv.(ProgressTracker.Votes')) in
         (do: # result_ptr <-[quorum.VoteResult] "$r0") ;;;
         return: (![go.int] (# granted_ptr), ![go.int] (# rejected_ptr),
                  ![quorum.VoteResult] (# result_ptr))

       with ["granted" ∷ granted_ptr ↦ W64 (nsat Pgr keys)] and
       ["rejected" ∷ rejected_ptr ↦ W64 (nsat Prj keys)] in hand, and [Hgfin] /
       [Hrfin] identifying those counts with the model's.  See the note above
       the statement for why the call cannot be stepped. *)
  Admitted.

End ProgressTrackerTallyVotesProof.
