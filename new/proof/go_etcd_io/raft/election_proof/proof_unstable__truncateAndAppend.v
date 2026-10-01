Require Export New.proof.go_etcd_io.raft.election_proof.postulates_unstable__truncateAndAppend.

Module UnstableTruncateAndAppendProof
  (P : UNSTABLE__TRUNCATEANDAPPEND_POSTULATES) : UNSTABLE__TRUNCATEANDAPPEND.
Import P.

  (** The three arms of the [switch], in order; see the spec.  The [Infof]
      of arms 2 and 3 is [wp_Logger__logf] on [u.logger], read through
      [u ↦ uv].  Arm 3's [keep] is capped ([u.slice] returns
      [entries[a:b:b]]), so its [own_slice_cap] is free
      ([own_slice_cap_empty]) and the [append] reallocates; arm 3's
      [min] needs the [go.min] unfolding of notes/gotchas.md. *)
  Lemma wp_unstable__truncateAndAppend :
    wp_unstable__truncateAndAppend_body.
  Proof.
    intros_ambient.
    intros u uv uents ents e0 es dq ulg.
    intros Hfirst Hle Hnw Hulg. wp_start as "H". iNamed "H". iNamed "Hun".
    (* name the adopt condition, so that the [bool_decide] rewrites below
       cannot hit the copies in ["Hadopt"] and the postcondition *)
    set (adopt := bool_decide ((uint.Z e0.(raftpb.Entry.Index') ≤ uint.Z uv.(raft.unstable.offset'))%Z ∧
                               (uint.Z e0.(raftpb.Entry.Index')
                                ≠ uint.Z uv.(raft.unstable.offset') + Z.of_nat (length uents))%Z)%type).
    wp_auto.
    iDestruct (own_slice_len with "Hes") as %[Hlen Hlen'].
    iDestruct (own_slice_len with "Hents") as %[Hulen Hulen'].
    (* [ents[0].Index]: hand the element out of the slice for the field load *)
    assert (0 < length ents)%nat as Hne
      by (apply lookup_lt_is_Some_1; eauto).
    rewrite decide_True; last word.
    iDestruct (own_slice_elem_acc 0 e0 es dq ents with "Hes")
      as "[He0 Hesback]"; [ word | exact Hfirst | ].
    wp_auto.
    iDestruct ("Hesback" with "He0") as "Hes".
    rewrite list_insert_id //.
    destruct (decide (uint.Z e0.(raftpb.Entry.Index')
                      = uint.Z uv.(raft.unstable.offset') + Z.of_nat (length uents))%Z)
      as [Hcont|Hncont].
    - (* arm 1: the batch continues the suffix *)
      assert (e0.(raftpb.Entry.Index')
              = word.add uv.(raft.unstable.offset')
                  uv.(raft.unstable.entries').(slice.len)) as Hguard by word.
      rewrite Hguard !bool_decide_eq_true_2 //.
      wp_auto.
      assert (adopt = false) as Had by (apply bool_decide_eq_false_2; lia).
      rewrite Had.
      iClear "Hadopt".
      wp_apply (wp_slice_append_persistent with "[$Hents $Hents_cap $Hes]")
        as "%sl (Hents & Hents_cap & Hes)".
      iApply ("HΦ" $! (uv <| raft.unstable.entries' := sl |>)).
      rewrite take_ge; last word.
      rewrite /own_unstable. iFrame. iPureIntro. simpl. split_and!; [word|done|done].
    - rewrite (bool_decide_eq_false_2 (e0.(raftpb.Entry.Index') =
                  word.add uv.(raft.unstable.offset') uv.(raft.unstable.entries').(slice.len)));
        last (intros Heq; apply Hncont; rewrite Heq; word).
      rewrite bool_decide_eq_false_2 //.
      wp_auto.
      destruct (decide (uint.Z e0.(raftpb.Entry.Index')
                        ≤ uint.Z uv.(raft.unstable.offset'))%Z) as [Hrep|Htr].
      + (* arm 2: replace the suffix, adopting the caller's slice *)
        rewrite (bool_decide_eq_true_2 (uint.Z e0.(raftpb.Entry.Index')
                                          ≤ uint.Z uv.(raft.unstable.offset'))%Z); last done.
        rewrite bool_decide_eq_true_2 //.
        assert (adopt = true) as Had by (apply bool_decide_eq_true_2; split; [done | exact Hncont]).
        rewrite Had.
        iDestruct "Hadopt" as "[-> Hcap]".
        wp_auto.
        wp_apply wp_slice_literal.
        try (iSplitR; [ done | ]); try iIntros "% [? _]"; try wp_auto.
        rewrite Hulg. try wp_auto.
        wp_apply (wp_Logger__logf with "Hlg"); first solve_log_method.
        try wp_auto.
        iApply ("HΦ" $! (uv <| raft.unstable.entries' := es |>
                            <| raft.unstable.offset' := e0.(raftpb.Entry.Index') |>
                            <| raft.unstable.offsetInProgress' := e0.(raftpb.Entry.Index') |>)).
        replace (Z.to_nat (uint.Z e0.(raftpb.Entry.Index') - uint.Z uv.(raft.unstable.offset')))
          with 0%nat by lia.
        rewrite take_0 app_nil_l.
        rewrite /own_unstable. iFrame. iSplit; [|done].
        iPureIntro. simpl. split_and!; [lia|done|done].
      + (* arm 3: keep the suffix below [fromIndex], then append *)
        rewrite (bool_decide_eq_false_2 (uint.Z e0.(raftpb.Entry.Index')
                                           ≤ uint.Z uv.(raft.unstable.offset'))%Z); last done.
        rewrite bool_decide_eq_false_2 //.
        assert (adopt = false) as Had by (apply bool_decide_eq_false_2; intros [Hc _]; lia).
        rewrite Had.
        iClear "Hadopt".
        wp_auto.
        wp_apply wp_slice_literal.
        try (iSplitR; [ done | ]); try iIntros "% [? _]"; try wp_auto.
        rewrite Hulg. try wp_auto.
        wp_apply (wp_Logger__logf with "Hlg"); first solve_log_method.
        try wp_auto.
        assert (Hus : (uint.Z uv.(raft.unstable.offset') ≤ uint.Z uv.(raft.unstable.offset') ∧
                       uint.Z uv.(raft.unstable.offset') < uint.Z e0.(raftpb.Entry.Index') ∧
                       uint.Z e0.(raftpb.Entry.Index')
                       ≤ uint.Z uv.(raft.unstable.offset') + Z.of_nat (length uents))%Z) by lia.
        wp_apply (wp_unstable__slice _ _ _ _ _ Hus Hnw with "[Hu Hents Hents_cap]")
          as "%s0 %es0 ((Hu & Hents_cap & Hents) & #Hs0 & (%Hlen0 & %Hin0 & %Hcap0 & %Hes0))".
        { rewrite /own_unstable. iFrame. }
        rewrite /subslice Z.sub_diag /= drop_0 in Hes0. subst es0.
        iDestruct (own_slice_len with "Hs0") as %[Hs0len Hs0len'].
        iDestruct (own_slice_cap_empty (V:=raftpb.Entry.t) s0) as "Hs0cap"; [done | word |].
        wp_apply (wp_slice_append_persistent with "[$Hes $Hs0 $Hs0cap]")
          as "%sl (Hsl & Hsl_cap & Hes)".
        change ([go.uint64; go.uint64]) with (replicate 2 go.uint64).
        rewrite func_unfold /minⁱᵐᵖˡ.
        wp_auto.
        case_bool_decide; wp_auto.
        all: iApply ("HΦ" $! (uv <| raft.unstable.entries' := sl |>
                                 <| raft.unstable.offsetInProgress' := _ |>)).
        all: rewrite /own_unstable; iFrame "Hu Hsl Hsl_cap Hes"; iPureIntro.
        all: simpl; split_and!; [lia|done|done].
  Qed.

End UnstableTruncateAndAppendProof.
