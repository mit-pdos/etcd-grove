Require Export New.proof.go_etcd_io.raft.election_proof.postulates_unstable__truncateAndAppend.

Module UnstableTruncateAndAppendProof
  (P : UNSTABLE__TRUNCATEANDAPPEND_POSTULATES) : UNSTABLE__TRUNCATEANDAPPEND.

  Lemma wp_unstable__truncateAndAppend :
    wp_unstable__truncateAndAppend_body.
  Proof.
    intros_ambient.
    intros u uv uents ents e0 es dq.
    intros Hfirst Hcont. wp_start as "H". iNamed "H". iNamed "Hun". wp_auto.
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
    (* the guard: the batch continues the suffix *)
    assert (e0.(raftpb.Entry.Index')
            = word.add uv.(raft.unstable.offset')
                uv.(raft.unstable.entries').(slice.len)) as Hguard by word.
    rewrite Hguard !bool_decide_eq_true_2 //.
    wp_auto.
    wp_apply (wp_slice_append_persistent with "[$Hents $Hents_cap $Hes]")
      as "%sl (Hents & Hents_cap & Hes)".
    iApply "HΦ". rewrite /own_unstable. iFrame.
  Qed.

End UnstableTruncateAndAppendProof.
