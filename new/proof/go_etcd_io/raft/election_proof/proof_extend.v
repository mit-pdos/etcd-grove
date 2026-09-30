Require Export New.proof.go_etcd_io.raft.election_proof.postulates_extend.

Module ExtendProof (P : EXTEND_POSTULATES) : EXTEND.

  (** The in-place [append] branch is dead by the [cap] premise; what is
      left is [make(need, need)], a [copy] of [dst] into the front and a
      [copy] of [vals] into the tail sub-slice [buf[len(dst):]].

      Two things to watch.  (1) [need = len(dst) + len(vals)] is a [w64]
      [add]: [Hneed] pins [sint (dst.len + vals.len) = |ds| + |vs|] from the
      [Hfits] premise, and rewriting with it up front keeps every later
      [take]/[drop]/[replicate] index a plain [nat] so [lia] can see them.
      (2) [buf[len(dst):]] is a [slice.slice], and [wp_slice_copy]'s [st]
      cannot be inferred until the goal has actually been stepped to the
      call, hence the [wp_auto] before the second [copy] (the bounds
      [decide] must be discharged first, or [wp_auto] stops at it).

      The tail is split off with [own_slice_split_all] and put back with
      [own_slice_combine] plus [own_slice_trivial_slice_2]; the [⊣⊢] form of
      [own_slice_split_all] only runs left to right under [iDestruct]. *)
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
    assert (Hneed : (Z.to_nat (sint.Z (word.add dst.(slice.len) vals.(slice.len)))
                     = length ds + length vs)%nat) by word.
    rewrite Hneed.
    wp_apply (wp_slice_copy with "[$Hbuf $Hdst]") as "%n1 (%Hn1 & Hbuf & Hdst)".
    rewrite length_replicate take_ge; last lia.
    rewrite drop_replicate.
    replace (length ds + length vs - length ds)%nat with (length vs) by lia.
    iDestruct (own_slice_len with "Hbuf") as %[Hlenb Hlenb'].
    rewrite length_app length_replicate in Hlenb.
    case_decide as Hdec; [clear Hdec | exfalso; apply Hdec; word].
    iDestruct (own_slice_split_all dst.(slice.len) with "Hbuf") as "[Hbuf1 Hbuf2]";
      first word.
    rewrite take_app_length'; last lia.
    rewrite drop_app_length'; last lia.
    wp_auto.
    wp_apply (wp_slice_copy (V:=raftpb.Entry.t) (t:=raftpb.Entry)
                with "[$Hbuf2 $Hvals]") as "%n2 (%Hn2 & Hbuf2 & Hvals)".
    rewrite length_replicate take_ge; last lia.
    rewrite drop_replicate Nat.sub_diag /= app_nil_r.
    iDestruct (own_slice_combine dst.(slice.len) buf (DfracOwn 1) ds vs
                 (W64 0) buf.(slice.len) with "Hbuf1 Hbuf2") as "Hbuf";
      first (split; word).
    iDestruct (own_slice_trivial_slice_2 with "Hbuf") as "Hbuf".
    iApply "HΦ". iFrame.
  Qed.

End ExtendProof.
