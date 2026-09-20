Require Export New.proof.go_etcd_io.raft.v3_proof.election.postulates_extend.

Module ExtendProof (P : EXTEND_POSTULATES) : EXTEND.

  (** The in-place [append] branch is dead by the [cap] premise; what is
      left is [make(need, need)], a [copy] of [dst] into the front and a
      [copy] of [vals] into the tail sub-slice [buf[len(dst):]].  The tail is
      split off with [own_slice_split_all] and put back the same way. *)
  Lemma wp_extend : wp_extend_body.
  Proof.
    intros_ambient.
    intros dst vals ds vs dq1 dq2 Hcap Hfits.
    wp_start as "H". iNamed "H". wp_auto.
    iDestruct (own_slice_len with "Hdst") as %[Hlen1 Hlen1'].
    iDestruct (own_slice_len with "Hvals") as %[Hlen2 Hlen2'].
    rewrite bool_decide_eq_false_2; last word. wp_auto.
    wp_apply (wp_slice_make3 (V:=raftpb.Entry.t) (t:=raftpb.Entry))
      as "%buf (Hbuf & Hbuf_cap & %Hbufcap)"; first word.
    wp_apply (wp_slice_copy with "[$Hbuf $Hdst]") as "%n1 (%Hn1 & Hbuf & Hdst)".
    rewrite length_replicate.
    iDestruct (own_slice_len with "Hbuf") as %[Hlenb Hlenb'].
    rewrite decide_True; last word.
    iDestruct (own_slice_split_all dst.(slice.len) with "Hbuf") as "[Hbuf1 Hbuf2]";
      first word.
    wp_apply (wp_slice_copy with "[$Hbuf2 $Hvals]") as "%n2 (%Hn2 & Hbuf2 & Hvals)".
    iDestruct (own_slice_split_all dst.(slice.len) buf with "[$Hbuf1 $Hbuf2]") as "Hbuf";
      first word.
    iApply "HΦ". iFrame.
    iExactEq "Hbuf". f_equal.
    rewrite -Hlen1.
    rewrite take_app_length' ; last (rewrite length_take length_app length_replicate; lia).
    admit.
  Admitted.

End ExtendProof.
