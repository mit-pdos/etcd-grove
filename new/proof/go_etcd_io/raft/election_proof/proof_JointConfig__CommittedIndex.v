Require Export New.proof.go_etcd_io.raft.election_proof.postulates_JointConfig__CommittedIndex.

Module JointConfigCommittedIndexProof (P : JOINTCONFIG__COMMITTEDINDEX_POSTULATES)
  : JOINTCONFIG__COMMITTEDINDEX.
Import P.

  (** The receiver is a value-receiver copy [c]: [c[0]] and [c[1]] are
      handed to [MajorityConfig.CommittedIndex] one after the other, the
      voter map and the indexer's resource lent to the first; [c[1]] is
      the nil component, whose answer is [MaxUint64]; then [min].  The
      array element reads go through [array_acc], as in
      [proof_JointConfig__VoteResult.v]. *)
  Lemma wp_JointConfig__CommittedIndex : wp_JointConfig__CommittedIndex_body.
  Proof.
  intros_ambient.
  intros c a m0 ids l PP acked.
  wp_start as "(Hsz & Hc & %Harr & Hm0 & #Hidx & HP)".
  wp_auto.
  wp_method_call. wp_call. wp_call.
  wp_auto.
  iDestruct (array_acc _ 0 with "c") as "[Hc0 Hcback]".
  { done. }
  { rewrite Harr. done. }
  (* the voter map is a real map, so the callee's [map.nil] disjunct
     cannot come back for it *)
  iDestruct (own_map_not_nil with "Hm0") as %Hvnn.
  wp_apply (wp_MajorityConfig__CommittedIndex (dom ids) with "[$Hc0 $Hsz $Hidx $HP Hm0]").
  { iRight. iExists ids. by iFrame. }
  iIntros (N0) "(Hc0 & Hv & HP & %Hemp0 & %Hq0)".
  iDestruct "Hv" as "[[%Hnil _]|(%voters' & %Hvoters'_dom & Hvoters)]".
  { exfalso. by apply Hvnn. }
  wp_auto.
  (* [c[1]]: the nil component of a simple configuration *)
  iDestruct ("Hcback" with "Hc0") as "c".
  rewrite Harr /=.
  iDestruct (array_acc _ 1 with "c") as "[Hc1 Hcback]".
  { done. }
  { done. }
  iAssert (⌜ Z.of_nat (size (∅ : gset w64)) < 2 ^ 63 ⌝)%I as "Hsz1".
  { iPureIntro. rewrite size_empty. lia. }
  wp_apply (wp_MajorityConfig__CommittedIndex ∅ with "[$Hc1 $Hsz1 $Hidx $HP]").
  { by iLeft. }
  iIntros (N1) "(Hc1 & _ & HP & %Hemp1 & _)".
  assert (N1 = W64 (2 ^ 64 - 1)) as -> by (by apply Hemp1).
  iDestruct ("Hcback" with "Hc1") as "c".
  wp_auto.
  (* [min]: [c[0]]'s answer on both exits *)
  case_bool_decide as Hlt; wp_auto.
  - iApply "HΦ". iFrame "Hc HP". iSplitL "Hvoters".
    { iExists voters'. by iFrame. }
    iPureIntro. split; [exact Hemp0 | exact Hq0].
  - assert (N0 = W64 (2 ^ 64 - 1)) as Heq by word.
    iApply "HΦ". iFrame "Hc HP". iSplitL "Hvoters".
    { iExists voters'. by iFrame. }
    rewrite -Heq. iPureIntro.
    split; [done | exact Hq0].
  Qed.

End JointConfigCommittedIndexProof.
