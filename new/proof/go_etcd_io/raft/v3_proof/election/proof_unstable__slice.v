Require Export New.proof.go_etcd_io.raft.v3_proof.election.postulates_unstable__slice.

Module UnstableSliceProof (P : UNSTABLE__SLICE_POSTULATES) : UNSTABLE__SLICE.
Import P.

  (** After the bounds check the whole body is one three-index slice
      expression.  Goose renders [u.entries[a:b:b]] as
      [slice.full_slice entries V a b b], whose [cap] is [b - a] -- equal to
      its [len], which is the [cap = len] the postcondition promises and
      which [raftLog.slice] needs so that [extend] reallocates.  The
      ownership lemmas ([own_slice_slice]) only speak about
      [slice.slice entries V a b], whose [cap] is [entries.cap - a]; the two
      agree on pointer and length, so [own_slice_same_ptr_len]
      ([inv_raftlog.v]) carries the points-to across, in both directions
      (out, and back inside the wand).  That lemma needs a non-empty list,
      which is why the spec demands [lo < hi].

      Note the explicit [s], [dq] and [vs] on the closing
      [rewrite (own_slice_slice ...)]: without them the setoid rewrite
      matches the first [_ ↦*{_} _] in the *context* (the [take] half) and
      leaves an unprovable side condition. *)
  Lemma wp_unstable__slice : wp_unstable__slice_body.
  Proof.
    intros_ambient.
    intros u uv uents lo hi Hrange Hnw.
    destruct Hrange as (Hr1 & Hr2 & Hr3).
    assert (Hrange' : (uint.Z uv.(raft.unstable.offset') ≤ uint.Z lo ≤ uint.Z hi ≤
                       uint.Z uv.(raft.unstable.offset') + Z.of_nat (length uents))%Z)
      by lia.
    wp_start as "H". iNamed "H".
    iDestruct (own_slice_len with "Hents") as %[Hlen Hlen'].
    iDestruct (own_slice_wf with "Hents") as %Hwf.
    wp_auto.
    wp_apply (wp_unstable__mustCheckOutOfBounds _ _ _ (DfracOwn 1) _ _ Hrange' Hnw
                with "[$Hu $Hents]") as "[Hu Hents]".
    rewrite decide_True; last word.
    wp_auto.
    set (lo' := word.sub lo uv.(raft.unstable.offset')).
    set (hi' := word.sub hi uv.(raft.unstable.offset')).
    assert (Hlo' : sint.Z lo' = (uint.Z lo - uint.Z uv.(raft.unstable.offset'))%Z)
      by (subst lo'; word).
    assert (Hhi' : sint.Z hi' = (uint.Z hi - uint.Z uv.(raft.unstable.offset'))%Z)
      by (subst hi'; word).
    assert (Hsublen : length (subslice (sint.nat lo') (sint.nat hi') uents)
                      = (sint.nat hi' - sint.nat lo')%nat)
      by (apply subslice_length; word).
    iDestruct (own_slice_slice lo' hi' with "Hents") as "(H1 & H2 & H3)"; first word.
    iDestruct (own_slice_same_ptr_len
                 (slice.slice uv.(raft.unstable.entries') raftpb.Entry.t lo' hi')
                 (slice.full_slice uv.(raft.unstable.entries') raftpb.Entry.t lo' hi' hi')
                 with "H2") as "Hs".
    { intros Hc. rewrite Hc /= in Hsublen. word. }
    { done. }
    { done. }
    { simpl. lia. }
    iApply ("HΦ" $! _ (subslice (sint.nat lo') (sint.nat hi') uents)).
    iFrame "Hu Hs".
    iSplitR.
    { iPureIntro. split_and!.
      - rewrite Hsublen. word.
      - intros e He. apply list_elem_of_lookup_1 in He as [i Hi].
        assert (Hib : (i < sint.nat hi' - sint.nat lo')%nat).
        { apply lookup_lt_Some in Hi. lia. }
        rewrite subslice_lookup in Hi; last lia.
        eapply list_elem_of_lookup_2. exact Hi.
      - done. }
    iIntros "Hs".
    iDestruct (own_slice_same_ptr_len
                 (slice.full_slice uv.(raft.unstable.entries') raftpb.Entry.t lo' hi' hi')
                 (slice.slice uv.(raft.unstable.entries') raftpb.Entry.t lo' hi')
                 with "Hs") as "H2".
    { intros Hc. rewrite Hc /= in Hsublen. word. }
    { done. }
    { done. }
    { simpl. word. }
    rewrite (own_slice_slice lo' hi' uv.(raft.unstable.entries') (DfracOwn 1) uents);
      last word.
    iFrame.
  Qed.

End UnstableSliceProof.
