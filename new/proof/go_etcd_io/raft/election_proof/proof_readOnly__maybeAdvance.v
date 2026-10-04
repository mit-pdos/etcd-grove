Require Export New.proof.go_etcd_io.raft.election_proof.postulates_readOnly__maybeAdvance.

Module ReadOnlyMaybeAdvanceProof (P : READONLY__MAYBEADVANCE_POSTULATES)
  : READONLY__MAYBEADVANCE.
Import P.

  Lemma big_sepL2_take_drop {PROP : bi} {A B : Type} (Φ : A → B → PROP)
      (n : nat) (l1 : list A) (l2 : list B) :
    length l1 = length l2 →
    ([∗ list] x;y ∈ l1;l2, Φ x y) ⊢
    ([∗ list] x;y ∈ take n l1;take n l2, Φ x y) ∗
    ([∗ list] x;y ∈ drop n l1;drop n l2, Φ x y).
  Proof.
    intros Hl. rewrite -{1}(take_drop n l1) -{1}(take_drop n l2).
    apply big_sepL2_app_inv. left. rewrite !length_take. lia.
  Qed.

  Lemma readonly_advance_le (r : readonly.t) (N : w64) :
    uint.Z N ≤ uint.Z r.(readonly.confirmed) → readonly_advance r N = (r, []).
  Proof. intros H. rewrite /readonly_advance. by case_decide. Qed.

  Lemma readonly_advance_gt (r : readonly.t) (N : w64) :
    ¬ uint.Z N ≤ uint.Z r.(readonly.confirmed) →
    readonly_advance r N =
      (r <| readonly.pending := drop (uint.nat (word.sub N r.(readonly.confirmed)))
                                  r.(readonly.pending) |>
         <| readonly.confirmed := N |>,
       take (uint.nat (word.sub N r.(readonly.confirmed))) r.(readonly.pending)).
  Proof. intros H. rewrite /readonly_advance. by case_decide. Qed.

  (** [CommittedIndex] is called on the object itself, as an
      [AckedIndexer], with the whole object as the indexer's resource and
      the voter map lent (the receiver is the local copy of [c]).  Then, if
      the quorum index is past [confirmedReads], the first [N - confirmed]
      requests are split off the queue ([own_slice_slice] at [↦*□]): the
      slice returned is that prefix, read-only and without the capacity;
      the rest, with the capacity ([own_slice_cap_slice]), is the new
      queue. *)
  Lemma wp_readOnly__maybeAdvance : wp_readOnly__maybeAdvance_body.
  Proof.
    intros_ambient.
    intros ro r c m0 ids.
    wp_start as "Hown". iNamed "Hown".
    wp_auto.
    (* the indexer's contract, from [readOnly.AckedIndex]'s triple, with the
       whole object as its resource *)
    iAssert (is_AckedIndexer
               (interface.mk_ok (go.PointerType raft.readOnly) #ro)
               (own_ReadOnly ro r) (λ v, r.(readonly.acks) !! v))%I as "#Hidx".
    { iExists _. iSplit; first done.
      iIntros "!>" (id Ψ) "!> HP HΨ". simpl.
      wp_apply (wp_readOnly__AckedIndex with "[$HP]") as "HP".
      by iApply "HΨ". }
    wp_apply (wp_JointConfig__CommittedIndex c_ptr c m0 ids
                (interface.mk_ok (go.PointerType raft.readOnly) #ro)
                (own_ReadOnly ro r) (λ v, r.(readonly.acks) !! v)
                with "[$c $Hvoters $Hown $Hidx]") as "%N (c & Hv & Hown & %Hemp & %Hq)".
    { iPureIntro. split; first done. done. }
    iNamed "Hown".
    wp_auto.
    iDestruct (own_slice_len with "Hucr") as %[Hl Hl0].
    iDestruct (own_slice_wf with "Hucr") as %Hwf.
    iDestruct (big_sepL2_length with "Hreqs") as %Hlen.
    wp_if_destruct.
    - (* nothing confirmed: [nil] *)
      iApply ("HΦ" $! slice.nil N).
      rewrite readonly_advance_le; last by rewrite -Hro_conf.
      simpl.
      iSplit; first (iPureIntro; by apply Hq).
      iFrame "Hv". iSplitL "Hro Hacks Hucr Hucr_cap Hreqs".
      { iExists rov, ptrs. iFrame. done. }
      iExists []. iSplit; first iApply own_slice_nil. done.
    - (* [N] is one of the acknowledged positions, so at most
         [confirmed + len pending] *)
      pose proof (Hq Hne) as ((v & Hv & HNv) & _ & _).
      assert (HNle : uint.Z N ≤ uint.Z r.(readonly.confirmed) + length r.(readonly.pending)).
      { rewrite -HNv. by apply Hbound. }
      rewrite -Hro_conf in HNle.
      assert (HlenZ : Z.of_nat (length ptrs)
                      = sint.Z rov.(raft.readOnly.unconfirmedReads').(slice.len)).
      { rewrite Hl. apply Z2Nat.id. exact Hl0. }
      assert (HsubZ : uint.Z (word.sub N rov.(raft.readOnly.confirmedReads'))
                      = uint.Z N - uint.Z rov.(raft.readOnly.confirmedReads')) by word.
      assert (HkZ : uint.Z (word.sub N rov.(raft.readOnly.confirmedReads'))
                    ≤ sint.Z rov.(raft.readOnly.unconfirmedReads').(slice.len)).
      { rewrite HsubZ -HlenZ Hlen. lia. }
      assert (Hk : uint.nat (word.sub N rov.(raft.readOnly.confirmedReads'))
                   ≤ length ptrs).
      { assert (uint.Z (word.sub N rov.(raft.readOnly.confirmedReads')) ≤ Z.of_nat (length ptrs))
          by (rewrite HlenZ; exact HkZ).
        word. }
      rewrite -> decide_True; last word.
      wp_auto.
      rewrite -> decide_True; last word.
      wp_auto.
      iDestruct (own_slice_slice (word.sub N rov.(raft.readOnly.confirmedReads')) rov.(raft.readOnly.unconfirmedReads').(slice.len)
                   with "Hucr") as "(Hpre & Hrest & _)".
      { word. }
      iDestruct (own_slice_cap_slice _ (word.sub N rov.(raft.readOnly.confirmedReads')) with "Hucr_cap") as "Hcap".
      { word. }
      rewrite subslice_to_end.
      2:{ word. }
      iDestruct (big_sepL2_take_drop _ (uint.nat (word.sub N rov.(raft.readOnly.confirmedReads')))
                   with "Hreqs") as "[Hreqs1 Hreqs2]".
      { exact Hlen. }
      assert (Hku : sint.Z (word.sub N rov.(raft.readOnly.confirmedReads'))
                    = uint.Z (word.sub N rov.(raft.readOnly.confirmedReads'))) by word.
      rewrite Hku.
      iApply ("HΦ" $! _ N).
      rewrite readonly_advance_gt; last by rewrite -Hro_conf.
      rewrite -Hro_conf. simpl.
      iSplit; first (iPureIntro; by apply Hq).
      iFrame "Hv". iSplitL "Hro Hacks Hrest Hcap Hreqs2".
      { iExists _, (drop (uint.nat (word.sub N rov.(raft.readOnly.confirmedReads'))) ptrs).
        iFrame "Hro". simpl. iFrame "Hacks Hrest Hcap Hreqs2".
        iPureIntro. split; done. }
      iExists _. iFrame "Hpre Hreqs1".
  Qed.

End ReadOnlyMaybeAdvanceProof.
