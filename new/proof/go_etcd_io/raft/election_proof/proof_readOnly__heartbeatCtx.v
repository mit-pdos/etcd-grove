Require Export New.proof.go_etcd_io.raft.election_proof.postulates_readOnly__heartbeatCtx.

Module ReadOnlyHeartbeatCtxProof (P : READONLY__HEARTBEATCTX_POSTULATES)
  : READONLY__HEARTBEATCTX.

  (** The length test is [pending = []] ([Hreqs] ties the queue to it); the
      other exit makes the eight bytes and fills them in. *)
  Lemma wp_readOnly__heartbeatCtx : wp_readOnly__heartbeatCtx_body.
  Proof.
    intros_ambient.
    intros ro r.
    wp_start as "Hown". iNamed "Hown". iNamed "Hown".
    iDestruct (own_slice_len with "Hucr") as %[Hl Hl0].
    iDestruct (big_sepL2_length with "Hreqs") as %Hlen.
    wp_auto.
    destruct (decide (r.(readonly.pending) = [])) as [Hnil|Hne].
    - rewrite Hnil in Hlen. simpl in Hlen.
      rewrite bool_decide_eq_true_2; last (simpl in Hl; word).
      wp_auto.
      iApply "HΦ". iSplitL "Hro Hacks Hucr Hucr_cap Hreqs"; last (iLeft; done).
      iExists rov, ptrs. iFrame. done.
    - rewrite bool_decide_eq_false_2.
      2:{ simpl in Hl. destruct (r.(readonly.pending)); [done|simpl in Hlen; word]. }
      wp_auto.
      wp_apply wp_slice_make2 as "%sl (Hsl & Hcap)".
      { word. }
      iDestruct (own_slice_wf with "Hucr") as %Hwf.
      assert (Hpos : word.add rov.(raft.readOnly.confirmedReads')
                       rov.(raft.readOnly.unconfirmedReads').(slice.len)
                     = readonly_position r).
      { rewrite /readonly_position -Hro_conf -Hlen.
        simpl in Hl. word. }
      rewrite Hpos.
      wp_apply (wp_LittleEndian_PutUint64 _ (replicate 8 (zero_val w8)) [] with "[Hsl]") as "Hsl".
      { by rewrite length_replicate. }
      { rewrite app_nil_r. iExactEq "Hsl". f_equal. }
      iApply "HΦ". iSplitL "Hro Hacks Hucr Hucr_cap Hreqs".
      { iExists rov, ptrs. iFrame. done. }
      iRight. iFrame. iSplit; first done.
      rewrite app_nil_r. done.
  Qed.

End ReadOnlyHeartbeatCtxProof.
