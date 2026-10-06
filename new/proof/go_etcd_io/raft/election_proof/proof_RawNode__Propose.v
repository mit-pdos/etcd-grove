Require Export New.proof.go_etcd_io.raft.election_proof.postulates_RawNode__Propose.

Module RawNodeProposeProof (P : RAWNODE__PROPOSE_POSTULATES) : RAWNODE__PROPOSE.
Import P.

  (** [Step] on the literal message: [Type: MsgProp], [From: r.id], the
      one-entry batch; every other field zero.  Its [MsgProp] arm, at the
      singleton batch, is the postcondition. *)
  Lemma wp_RawNode__Propose : wp_RawNode__Propose_body.
  Proof.
    intros_ambient.
    intros cfg γ rn rnv r id s ps data_sl data Q Hcfg Hin Hrel Hr.
    subst r.
    wp_start as "@".
    wp_auto.
    wp_apply (wp_raft_load_id with "Hphys") as "Hphys".
    try wp_auto.
    wp_apply wp_slice_literal. iSplitR; first done. iIntros "% [Hes Hcap]".
    wp_auto.
    match goal with |- context [slice.mk sl_ptr ?n ?c] => set (sl := slice.mk sl_ptr n c) end.
    iAssert (sl ↦* [prop_entry data_sl])%I with "[Hes]" as "Hes"; first done.
    wp_apply (wp_raft__Step cfg γ _ id s ps _ [prop_entry data_sl] [Q] Hcfg
               with "[$Hphys $Hghost Hes Hcap Hau]").
    all: try (intros Hc; exfalso; revert Hc; simpl; w32_ne).
    { (* a [MsgProp] is in scope *)
      rewrite /step_msg /step_msg_types /=. set_solver. }
    { done. }
    { intros _. simpl. split; [done|by right]. }
    { done. }
    { (* the message: its one-entry batch, owned; [Context] nil *)
      assert (Hp : W32 2 = MsgProp) by done.
      (* [simpl] decides [Type = MsgProp] *)
      simpl.
      iFrame "Hes Hcap Hau".
      iSplit; [iSplit|iSplit].
      - iPureIntro. intros _. split_and!; [done|by apply Forall_singleton|simpl; lia].
      - iIntros "!> %ty %Hty _". rewrite Hp mtype_of_MsgProp in Hty.
        injection Hty as <-. by rewrite /is_message /=.
      - iExists []. iSplit; [iApply own_slice_nil|]. iPureIntro.
        split; [done|intros Hc; exfalso; revert Hc; rewrite Hp; w32_ne].
      - iIntros "!> %Hc". exfalso. revert Hc. rewrite /= Hp. w32_ne. }
    iIntros (err s' ps') "(Hphys & Hghost & %Hrel' & %Href & Herr & Hprops)".
    simpl.
    wp_auto.
    iApply "HΦ". iFrame "Hrn Hphys Hghost".
    iSplit; first done. iSplit; first done.
    iDestruct "Hprops" as "[[%Hok Hout]|Hau]".
    - iLeft. iSplit; first done.
      iDestruct "Hout" as "[(%γp & Hp & Ht) _]".
      iExists γp. iFrame "Ht".
      (* the index [last + 1 + 0] *)
      iExactEq "Hp". f_equal. word.
    - iRight. iDestruct "Hau" as "[Hau _]". iFrame "Hau".
      iDestruct "Herr" as "[%Herr|[_ #Hd]]"; [iLeft; done|iRight; iFrame "Hd"].
  Qed.

End RawNodeProposeProof.
