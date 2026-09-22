Require Export New.proof.go_etcd_io.raft.election_proof.postulates_MajorityConfig__VoteResult.
(* [wp_MajorityConfig_len] / [wp_MajorityConfig_nil_len]: [len] of a map of a
   *named* type, and of the nil map.  Proof structure only; see the header of
   that file. *)
Require Import New.proof.go_etcd_io.raft.election_proof.proof_MajorityConfig__VoteResult_helpers.majority_len.

Module MajorityConfigVoteResultProof (P : MAJORITYCONFIG__VOTERESULT_POSTULATES)
  : MAJORITYCONFIG__VOTERESULT.

  (** Distinct [quorum.VoteResult] constants are distinct [w8]s; [defs.v]'s
      [w32_ne] is the same trick one width down. *)
  Ltac w8_ne :=
    intros Heq; apply (f_equal uint.Z) in Heq; vm_compute in Heq; discriminate.

  (** The three exits of [MajorityConfig.VoteResult], in the order the body
      takes them: [len(c) == 0] (both for the nil map and for a real empty
      one), then [votedCnt >= q], then [votedCnt + missing >= q], then
      [VoteLost].  The map range counts two things at once: [nsat Pgr] is
      [votedCnt] and [nsat Pms] is [missing], and [nsat_granted] /
      [nsat_missing] ([inv_tracker.v]) turn them into set cardinalities when
      the range is over.  See [spec_MajorityConfig__VoteResult.v] for the
      arithmetic. *)
  Lemma wp_MajorityConfig__VoteResult : wp_MajorityConfig__VoteResult_body.
  Proof.
  intros_ambient. intros s cref mref votes_ref dq votes.
  wp_start as "(%Hsz & Hc & Hvotes & Hm)".
  wp_auto.
  wp_method_call. wp_call. wp_call.
  wp_auto.
  iDestruct "Hm" as "[[-> ->] | (%ids & %Hids & Hids)]".
  { (* the nil component of a simple config: [len(c) == 0], so [VoteWon] *)
    wp_apply wp_MajorityConfig_nil_len.
    iApply ("HΦ" $! VoteWon). iFrame.
    iSplitR; first (iLeft; done).
    iPureIntro. split_and!; [ by left | done | ..]; intros Hne; by exfalso.
  }
  wp_apply (wp_MajorityConfig_len with "Hids") as "Hids".
  assert (size ids = size s) as Hsize by (rewrite -Hids size_dom //).
  rewrite Hsize.
  destruct (decide (s = (∅ : gset w64))) as [->|Hne].
  { (* a real but *empty* map: [len(c) == 0] too, so [VoteWon] again *)
    rewrite size_empty. wp_auto.
    iApply ("HΦ" $! VoteWon). iFrame "Hc Hvotes".
    iSplitL "Hids"; first (iRight; iExists ids; by iFrame).
    iPureIntro. split_and!; [ by left | done | .. ];
      intros Hemp; exfalso; by apply Hemp. }
  (* [len(c) == 0] is false: this component is non-empty *)
  assert (0 < size s)%nat as Hpos.
  { destruct (decide (0 < size s)%nat) as [|Hz]; first done.
    exfalso. apply Hne. apply leibniz_equiv. apply size_empty_inv. lia. }
  rewrite bool_decide_eq_false_2; last word.
  wp_auto.
  set (Pgr := (λ k, votes !! k = Some true) : w64 → Prop).
  set (Pms := (λ k, votes !! k = None) : w64 → Prop).
  set (Pmap := (λ (keys : list w64) (i : Z),
    ∃ (idv : w64),
      "%Hi" ∷ ⌜ 0 ≤ i ⌝ ∗
      "Hvotes" ∷ votes_ref ↦${dq} votes ∗
      "votes" ∷ votes_ptr ↦ votes_ref ∗
      "id" ∷ id_ptr ↦ idv ∗
      "votedCnt" ∷ votedCnt_ptr ↦ W64 (nsat Pgr (take (Z.to_nat i) keys)) ∗
      "missing" ∷ missing_ptr ↦ W64 (nsat Pms (take (Z.to_nat i) keys)))%I).
  wp_apply (wp_map_for_range Pmap with "Hids").
  iIntros (keys) "(%Hkset & %Hklen & %Hknodup)".
  iSplitL "Hvotes votes id votedCnt missing".
  { rewrite /Pmap. iExists (W64 0).
    rewrite take_0 /nsat filter_nil /=. iFrame. iPureIntro. lia. }
  iSplitL "".
  { iIntros "!>" (i key vv) "[%Hkey %Hvv] HP". rewrite /Pmap. iNamed "HP".
    assert (Z.to_nat (i + 1) = S (Z.to_nat i)) as Hsucc by lia.
    assert (take (Z.to_nat (i + 1)) keys = take (Z.to_nat i) keys ++ [key])
      as Htake.
    { rewrite Hsucc. by apply take_S_r. }
    assert (nsat Pgr (take (Z.to_nat i) keys) ≤ size s)%nat as HgB.
    { etrans; first apply nsat_le. rewrite length_take Hklen Hsize. lia. }
    assert (nsat Pms (take (Z.to_nat i) keys) ≤ size s)%nat as HmB.
    { etrans; first apply nsat_le. rewrite length_take Hklen Hsize. lia. }
    wp_auto.
    wp_apply (wp_map_lookup2 with "Hvotes"). iIntros "Hvotes".
    destruct (votes !! key) as [[|]|] eqn:Hvk.
    - (* granted *)
      assert (Pgr key) as HPg by (rewrite /Pgr Hvk //).
      assert (¬ Pms key) as HPm by (rewrite /Pms Hvk; congruence).
      rewrite bool_decide_eq_true_2; last by eexists.
      wp_auto.
      iRight. iLeft. iSplit; first done.
      iExists key. rewrite Htake !nsat_snoc.
      destruct (decide (Pgr key)); last done.
      destruct (decide (Pms key)); first done.
      rewrite Nat.add_0_r.
      replace (W64 (nsat Pgr (take (Z.to_nat i) keys) + 1)%nat)
        with (word.add (W64 (nsat Pgr (take (Z.to_nat i) keys))) (W64 1))
        by word.
      iFrame. iPureIntro. lia.
    - (* rejected: neither counter moves *)
      assert (¬ Pgr key) as HPg by (rewrite /Pgr Hvk; congruence).
      assert (¬ Pms key) as HPm by (rewrite /Pms Hvk; congruence).
      rewrite bool_decide_eq_true_2; last by eexists.
      wp_auto.
      iRight. iLeft. iSplit; first done.
      iExists key. rewrite Htake !nsat_snoc.
      destruct (decide (Pgr key)); first done.
      destruct (decide (Pms key)); first done.
      rewrite !Nat.add_0_r.
      iFrame. iPureIntro. lia.
    - (* no answer: [missing++; continue] *)
      assert (¬ Pgr key) as HPg by (rewrite /Pgr Hvk; congruence).
      assert (Pms key) as HPm by (rewrite /Pms Hvk //).
      rewrite bool_decide_eq_false_2; last by intros [? ?].
      wp_auto.
      iLeft. iSplit; first done.
      iExists key. rewrite Htake !nsat_snoc.
      destruct (decide (Pgr key)); first done.
      destruct (decide (Pms key)); last done.
      rewrite Nat.add_0_r.
      replace (W64 (nsat Pms (take (Z.to_nat i) keys) + 1)%nat)
        with (word.add (W64 (nsat Pms (take (Z.to_nat i) keys))) (W64 1))
        by word.
      iFrame. iPureIntro. lia. }
  (* the range is over: the two counters hold the whole tally *)
  iIntros "HP Hids". rewrite /Pmap. iNamed "HP".
  rewrite Nat2Z.id -Hklen firstn_all.
  assert ((list_to_set keys : gset w64) = s) as Hks
    by (rewrite Hkset Hids //).
  assert (nsat Pgr keys = size (granted votes ∩ s)) as Hgfin
    by (rewrite /Pgr; by apply nsat_granted).
  assert (nsat Pms keys = size (s ∖ dom votes)) as Hmfin
    by (rewrite /Pms; by apply nsat_missing).
  wp_auto.
  wp_apply (wp_MajorityConfig_len with "Hids") as "Hids".
  rewrite Hsize.
  (* [q := len(c)/2 + 1], then the two comparisons.  Everything below is
     arithmetic: [is_quorum_alt] is the bridge to the model. *)
  assert (nsat Pgr keys + nsat Pms keys = size (s ∖ rejected votes))%nat
    as Hgm.
  { rewrite Hgfin Hmfin size_cfg_minus_rejected //. }
  assert (size (s ∖ rejected votes) ≤ size s)%nat as Hsub.
  { apply subseteq_size. set_solver. }
  assert (nsat Pgr keys ≤ size s)%nat as HgB.
  { rewrite Hgfin. apply subseteq_size. set_solver. }
  assert ((s ∖ rejected votes) ∩ s = s ∖ rejected votes) as Hint by set_solver.
  (* [is_quorum_alt] divides in [nat], the program in [Z] *)
  assert (Z.of_nat (size s / 2)%nat = Z.of_nat (size s) / 2) as Hqnat
    by (rewrite Nat2Z.inj_div //).
  assert (sint.Z (word.divs (W64 (size s)) (W64 2)) = Z.of_nat (size s) / 2)
    as Hdiv.
  { rewrite (Automation.word.word_signed_divs_nowrap_pos
               (W64 (size s)) (W64 2) ltac:(split; word)).
    f_equal; word. }
  assert (sint.Z (word.add (word.divs (W64 (size s)) (W64 2)) (W64 1))
          = Z.of_nat (size s) / 2 + 1) as Hq by word.
  assert (sint.Z (W64 (nsat Pgr keys)) = Z.of_nat (nsat Pgr keys)) as Hgw
    by word.
  assert (sint.Z (word.add (W64 (nsat Pgr keys)) (W64 (nsat Pms keys)))
          = Z.of_nat (nsat Pgr keys) + Z.of_nat (nsat Pms keys)) as Hgmw
    by word.
  destruct (decide (Z.of_nat (size s) / 2 + 1 ≤ Z.of_nat (nsat Pgr keys)))
    as [Hwon|Hwon].
  { (* [votedCnt >= q]: a quorum granted *)
    rewrite bool_decide_eq_true_2; last by rewrite Hq Hgw.
    wp_auto.
    iApply ("HΦ" $! VoteWon). iFrame "Hc Hvotes".
    iSplitL "Hids"; first (iRight; iExists ids; by iFrame).
    iPureIntro. split_and!.
    - by left.
    - done.
    - intros _. split; last done. intros _.
      apply is_quorum_alt. rewrite -Hgfin. lia.
    - intros _. split; first w8_ne.
      intros Hnq. exfalso. apply Hnq. apply is_quorum_alt.
      rewrite Hint. lia. }
  rewrite bool_decide_eq_false_2; last by rewrite Hq Hgw.
  wp_auto.
  destruct (decide (Z.of_nat (size s) / 2 + 1
                    ≤ Z.of_nat (nsat Pgr keys) + Z.of_nat (nsat Pms keys)))
    as [Hpend|Hpend].
  { (* [votedCnt + missing >= q]: the election is still winnable *)
    rewrite bool_decide_eq_true_2; last by rewrite Hq Hgmw.
    wp_auto.
    iApply ("HΦ" $! VotePending). iFrame "Hc Hvotes".
    iSplitL "Hids"; first (iRight; iExists ids; by iFrame).
    iPureIntro. split_and!.
    - by right; right.
    - intros Heq. exfalso. by apply Hne.
    - intros _. split; first w8_ne.
      intros Hqg%is_quorum_alt. rewrite -Hgfin in Hqg. lia.
    - intros _. split; first w8_ne.
      intros Hnq. exfalso. apply Hnq. apply is_quorum_alt.
      rewrite Hint. lia. }
  rewrite bool_decide_eq_false_2; last by rewrite Hq Hgmw.
  wp_auto.
  (* [votedCnt + missing < q]: the candidate cannot still win *)
  iApply ("HΦ" $! VoteLost). iFrame "Hc Hvotes".
  iSplitL "Hids"; first (iRight; iExists ids; by iFrame).
  iPureIntro. split_and!.
  - by right; left.
  - intros Heq. exfalso. by apply Hne.
  - intros _. split; first w8_ne.
    intros Hqg%is_quorum_alt. rewrite -Hgfin in Hqg. lia.
  - intros _. split; last done. intros _.
    intros Hq'%is_quorum_alt. rewrite Hint in Hq'. lia.
Qed.

End MajorityConfigVoteResultProof.
