Require Export New.proof.go_etcd_io.raft.election_proof.postulates_MajorityConfig__CommittedIndex.
Require Import New.proof.go_etcd_io.raft.election_proof.proof_MajorityConfig__CommittedIndex_helpers.committed_index.

Module MajorityConfigCommittedIndexProof (P : MAJORITYCONFIG__COMMITTEDINDEX_POSTULATES)
  : MAJORITYCONFIG__COMMITTEDINDEX.
Import P.

  (** The two [len(c) == 0] exits (the nil component, and a real but empty
      map), then the main path in four phases: the [if] choosing the stack
      buffer or a heap slice is joined at "[srt] is [n] zeros"
      ([wp_if_join], as in [proof_ProgressTracker__Visit.v]); the map range
      fills [srt] from the right (invariant: after [k] voters, [srt] is
      [n - J] zeros followed by the [J] acknowledgements among them,
      reversed, and [i = n - 1 - J]); [slices.Sort]; the read at
      [pos = n - (n/2+1)].  [fill_perm] and [sorted_quorum_index]
      ([proof_MajorityConfig__CommittedIndex_helpers/committed_index.v]) turn
      the sorted slice into [is_quorum_index].  [len] of the named map type
      is stepped by [go.len_underlying], as in [majority_len.v]. *)
  Lemma wp_MajorityConfig__CommittedIndex : wp_MajorityConfig__CommittedIndex_body.
  Proof.
  intros_ambient. intros cs cref mref l Pres acked.
  wp_start as "(%Hsz & Hc & Hm & #Hl & HP)".
  wp_auto.
  wp_method_call. wp_call. wp_call.
  wp_auto.
  rewrite (go.len_underlying quorum.MajorityConfig).
  rewrite (go.is_underlying (t := quorum.MajorityConfig)
             (tunder := go.MapType go.uint64 (go.StructType []))).
  iDestruct "Hm" as "[[-> ->] | (%ids & %Hids & Hids)]".
  { (* the nil component: [len(c) == 0] *)
    wp_auto. iApply "HΦ". iFrame. iSplitR; first (iLeft; done).
    iPureIntro. split; first done. intros Hn. by exfalso. }
  wp_apply (wp_map_len with "Hids") as "Hids".
  (* [wp_if_join] below substitutes [cs := dom ids] anyway; do it now *)
  subst cs. rewrite -size_dom.
  destruct (decide (dom ids = ∅)) as [Hemp|Hne].
  { (* a real but empty map: [len(c) == 0] too *)
    rewrite Hemp size_empty. wp_auto. iApply "HΦ". iFrame "Hc HP".
    iSplitL "Hids"; first (iRight; iExists ids; by iFrame).
    iPureIntro. split; first done. intros Hn. by exfalso. }
  assert (0 < size (dom ids))%nat as Hpos.
  { destruct (decide (0 < size (dom ids))%nat) as [|Hz]; first done.
    exfalso. apply Hne. apply leibniz_equiv. apply size_empty_inv. lia. }
  rewrite bool_decide_eq_false_2; last word.
  wp_auto.
  iNamed "Hl". subst l.
  (* Both arms of the [if] end with [srt] an [n]-slot slice of zeros. *)
  wp_if_join (λ v, (∃ (sl : slice.t) (xs : list w64),
      ⌜ v = execute_val ⌝ ∗
      "n" ∷ n_ptr ↦ W64 (size (dom ids)) ∗
      "srt" ∷ srt_ptr ↦ sl ∗
      "Hsl" ∷ sl ↦* xs ∗
      "%Hxs" ∷ ⌜ xs = replicate (size (dom ids)) (W64 0) ⌝)%I) with "[n srt stk]".
  - (* fast path: [srt = stk[:n]] aliases the stack array *)
    rewrite decide_True; last word.
    wp_auto.
    iDestruct (slice_array with "stk") as "Hsl"; first (simpl; lia).
    iDestruct (own_slice_split_all (W64 (size (dom ids))) with "Hsl") as "[Hsl _]";
      first (simpl; word).
    iExists _, _. iFrame "n srt". iSplitR; first done.
    rewrite /slice.slice /slice_index_ref /=. iFrame "Hsl".
    iPureIntro.
    change [W64 0; W64 0; W64 0; W64 0; W64 0; W64 0; W64 0]
      with (replicate 7 (W64 0)).
    rewrite take_replicate. f_equal. word.
  - (* slow path: [srt = make([]uint64, n)] *)
    wp_apply (wp_slice_make2 (V:=w64) (t:=go.uint64)) as "%sl [Hsl _]"; first word.
    iExists _, _. iFrame. iPureIntro. split; first done.
    f_equal. word.
  - iIntros (v) "H". iDestruct "H" as (sl xs) "(-> & H)". iNamed "H". subst xs.
    wp_auto.
    iDestruct (own_slice_len with "Hsl") as "%Hsl_len".
    rewrite length_replicate in Hsl_len.
    (* The map range fills [srt] from the right: after [k] voters, the
       acknowledged ones among them, reversed, occupy the last slots and
       the rest are still [0]; [i] points at the last zero. *)
    set (Pmap := (λ (keys : list w64) (k : Z),
      ∃ (idv : w64),
        "%Hk" ∷ ⌜ 0 ≤ k ≤ Z.of_nat (size (dom ids)) ⌝ ∗
        "srt" ∷ srt_ptr ↦ sl ∗
        "Hsl" ∷ sl ↦* (replicate (size (dom ids)
                                  - length (omap acked (take (Z.to_nat k) keys))) (W64 0)
                       ++ reverse (omap acked (take (Z.to_nat k) keys))) ∗
        "i" ∷ i_ptr ↦ W64 (Z.of_nat (size (dom ids)) - 1
                            - Z.of_nat (length (omap acked (take (Z.to_nat k) keys)))) ∗
        "id" ∷ id_ptr ↦ idv ∗
        "l" ∷ l_ptr ↦ interface.ok i ∗
        "HP" ∷ Pres)%I).
    wp_apply (wp_map_for_range Pmap with "Hids").
    iIntros (keys) "(%Hkset & %Hklen & %Hknodup)".
    rewrite -size_dom in Hklen.
    destruct Hsl_len as [Hsl_len Hsl_len0].
    iSplitL "srt Hsl i id l HP".
    { rewrite /Pmap. iExists (W64 0).
      rewrite take_0 /= Nat.sub_0_r app_nil_r. iFrame.
      iSplitR; first (iPureIntro; lia).
      replace (W64 (Z.of_nat (size (dom ids)) - 1 - 0))
        with (word.sub (W64 (size (dom ids))) (W64 1)) by word.
      iFrame. }
    iSplitL "".
    { iIntros "!>" (k key vv) "[%Hkey %Hvv] HP". rewrite /Pmap. iNamed "HP".
      assert (Z.to_nat (k + 1) = S (Z.to_nat k)) as Hsucc by lia.
      assert (take (Z.to_nat (k + 1)) keys = take (Z.to_nat k) keys ++ [key])
        as Htake.
      { rewrite Hsucc. by apply take_S_r. }
      pose proof (lookup_lt_Some _ _ _ Hkey) as Hk_lt.
      pose proof (length_omap_le acked (take (Z.to_nat k) keys)) as HJle.
      rewrite length_take in HJle.
      wp_auto.
      wp_apply ("HAckedIndex" $! key with "HP") as "HP".
      rewrite Htake omap_app.
      destruct (acked key) as [a|] eqn:Hak; simpl.
      - (* acknowledged: [srt[i] = idx; i--] *)
        wp_auto.
        rewrite decide_True; last (rewrite min_l in HJle; [word | lia]).
        wp_auto.
        rewrite min_l in HJle; last lia.
        set (o := omap acked (take (Z.to_nat k) keys)) in *.
        wp_apply (wp_store_slice_index (V:=w64) (t:=go.uint64) sl _ _ a with "[$Hsl]").
        { iPureIntro. rewrite length_app length_replicate length_reverse. word. }
        iIntros "Hsl". wp_auto.
        iRight. iLeft. iSplit; first done.
        iExists key. rewrite Hak.
        replace (Z.to_nat (sint.Z (W64 (Z.of_nat (size (dom ids)) - 1 - Z.of_nat (length o)))))
          with (size (dom ids) - 1 - length o)%nat by word.
        replace (size (dom ids) - length o)%nat
          with (S (size (dom ids) - 1 - length o)) by lia.
        rewrite insert_replicate_last.
        rewrite reverse_app /= length_app /=.
        replace (size (dom ids) - (length o + 1))%nat
          with (size (dom ids) - 1 - length o)%nat by lia.
        replace (word.sub (W64 (Z.of_nat (size (dom ids)) - 1 - Z.of_nat (length o))) (W64 1))
          with (W64 (Z.of_nat (size (dom ids)) - 1 - Z.of_nat (length o + 1)%nat)) by word.
        iFrame. iPureIntro. lia.
      - (* not acknowledged: the slot stays [0] *)
        wp_auto.
        iRight. iLeft. iSplit; first done.
        iExists key. rewrite Hak app_nil_r. iFrame. iPureIntro. lia. }
    (* the range is over: [srt] holds every acknowledgement, zeros first *)
    iIntros "HP Hids". rewrite /Pmap. iNamed "HP".
    rewrite Nat2Z.id -size_dom -Hklen firstn_all Hklen.
    wp_auto.
    wp_apply (wp_slices_Sort with "[$Hsl]") as "%ys (Hsl & %Hperm & %Hsorted)".
    assert (ys ≡ₚ (λ v, default (W64 0) (acked v)) <$> keys) as Hperm'.
    { symmetry. rewrite fill_perm Hklen. exact Hperm. }
    assert (length ys = size (dom ids)) as Hys_len
      by (rewrite Hperm' length_fmap //).
    (* [pos := n - (n/2 + 1)] *)
    assert (sint.Z (word.divs (W64 (size (dom ids))) (W64 2))
            = Z.of_nat (size (dom ids)) / 2) as Hdiv.
    { rewrite (Automation.word.word_signed_divs_nowrap_pos
                 (W64 (size (dom ids))) (W64 2) ltac:(split; word)).
      f_equal; word. }
    assert (Z.of_nat (size (dom ids) / 2)%nat = Z.of_nat (size (dom ids)) / 2) as Hqnat
      by (rewrite Nat2Z.inj_div //).
    assert (size (dom ids) / 2 + 1 ≤ size (dom ids))%nat as Hhalf.
    { pose proof (Nat.div_mod_eq (size (dom ids)) 2).
      pose proof (Nat.mod_upper_bound (size (dom ids)) 2). lia. }
    assert (sint.Z (word.sub (W64 (size (dom ids)))
                     (word.add (word.divs (W64 (size (dom ids))) (W64 2)) (W64 1)))
            = Z.of_nat (size (dom ids) - (size (dom ids) / 2 + 1))%nat) as Hposw.
    { word. }
    assert (∃ y, ys !! (size (dom ids) - (size (dom ids) / 2 + 1))%nat = Some y)
      as [y Hy] by (apply lookup_lt_is_Some_2; lia).
    rewrite decide_True; last word.
    wp_apply (wp_load_slice_index (V:=w64) (t:=go.uint64) sl _ ys (DfracOwn 1) y
                with "[$Hsl]") as "Hsl".
    { word. }
    { iPureIntro. rewrite Hposw Nat2Z.id. exact Hy. }
    iApply "HΦ". iFrame "Hc HP".
    iSplitL "Hids"; first (iRight; iExists ids; by iFrame).
    iPureIntro. split; first (intros Hemp; by exfalso).
    intros _.
    eapply (sorted_quorum_index (dom ids) keys _ ys y); done.
  Qed.

End MajorityConfigCommittedIndexProof.
