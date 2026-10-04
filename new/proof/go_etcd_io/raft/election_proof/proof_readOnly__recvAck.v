Require Export New.proof.go_etcd_io.raft.election_proof.postulates_readOnly__recvAck.

Module ReadOnlyRecvAckProof (P : READONLY__RECVACK_POSTULATES)
  : READONLY__RECVACK.

  Lemma readonly_recvAck_nil r from : readonly_recvAck r from [] = r.
  Proof. rewrite /readonly_recvAck. by case_decide. Qed.

  Lemma readonly_recvAck_cons r from cs : cs ≠ [] →
    readonly_recvAck r from cs
    = r <| readonly.acks := <[from := w64_max (default (W64 0) (r.(readonly.acks) !! from))
                                              (le_to_u64 (take 8 cs))]>
                              r.(readonly.acks) |>.
  Proof. intros. rewrite /readonly_recvAck. by case_decide. Qed.

  Lemma wp_readOnly__recvAck : wp_readOnly__recvAck_body.
  Proof.
    intros_ambient.
    intros ro r from ctx cs dq.
    wp_start as "Hown". iNamed "Hown". iNamed "Hown".
    iDestruct (own_slice_len with "Hctx") as %[Hcl Hcl0].
    wp_auto.
    destruct (decide (cs = [])) as [->|Hne].
    - rewrite bool_decide_eq_true_2; last (simpl in Hcl; word).
      wp_auto.
      iApply "HΦ". iFrame "Hctx".
      rewrite readonly_recvAck_nil.
      iExists rov, ptrs. iFrame. done.
    - rewrite bool_decide_eq_false_2.
      2:{ simpl in Hcl. destruct cs; [done|simpl in Hcl; word]. }
      wp_auto.
      assert (Hcs8 : 8 ≤ length cs) by (destruct Hlen; done).
      wp_apply (wp_map_lookup1 with "Hacks") as "Hacks".
      wp_apply (wp_LittleEndian_Uint64 _ (take 8 cs) dq (drop 8 cs) with "[Hctx]") as "Hctx".
      { rewrite length_take. lia. }
      { rewrite take_drop. iFrame "Hctx". }
      wp_apply wp_max2_uint64.
      wp_apply (wp_map_insert with "Hacks") as "Hacks".
      rewrite take_drop.
      iApply "HΦ". iFrame "Hctx".
      rewrite readonly_recvAck_cons //.
      iExists rov, ptrs. iFrame "Hro Hucr Hucr_cap Hreqs".
      iSplit; first done. iSplit; first done.
      simpl.
      iExactEq "Hacks". f_equal.
  Qed.

End ReadOnlyRecvAckProof.
