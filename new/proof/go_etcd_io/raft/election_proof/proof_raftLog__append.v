Require Export New.proof.go_etcd_io.raft.election_proof.postulates_raftLog__append.

Section helper.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : raft.Assumptions}.

(** Split the [unstable] field out of [l ↦ lv], keeping a wand that accepts
    *any* new value for it.

    [inv_raftlog.v]'s [split_unstable] is not enough here: it pins the field
    at the value it had, and [truncateAndAppend] installs a new
    [entries] slice -- whose value is introduced by that call's own
    postcondition, i.e. after the [AccessStrict] store instance's evar was
    created.  Same situation and same fix as [raft_split_trk] in
    [proof_raft__reset.v]; see notes/gotchas.md, "The [AccessStrict] store
    instance cannot take a value the call has not produced yet". *)
Local Lemma raftLog_split_unstable (l : loc) (lv : raft.raftLog.t) :
  l ↦ lv -∗
  l.[raft.raftLog.t, "unstable"] ↦ lv.(raft.raftLog.unstable') ∗
  (∀ uv, l.[raft.raftLog.t, "unstable"] ↦ uv -∗
         l ↦ (lv <| raft.raftLog.unstable' := uv |>)).
Proof.
  iIntros "Hl".
  iEval (rewrite typed_pointsto_unseal /typed_pointsto_wrap /=) in "Hl".
  iDestruct "Hl" as "[Hf %Hnn]". iNamed "Hf".
  iFrame "unstable".
  iIntros (uv) "Huv".
  iEval (rewrite typed_pointsto_unseal /typed_pointsto_wrap /=).
  iFrame "∗%".
Qed.

End helper.

Module RaftLogAppendProof (P : RAFTLOG__APPEND_POSTULATES) : RAFTLOG__APPEND.
Import P.

  Lemma wp_raftLog__append_at : wp_raftLog__append_at_body.
  Proof.
    intros_ambient.
    intros l prev sents uents ents es dq.
    intros Hidx' Hnorm Hnowrap'. wp_start as "H". iNamed "H". wp_auto.
    iDestruct (own_slice_len with "Hes") as %[Hlen Hlen'].
    destruct (decide (ents = [])) as [He|Hne].
    - (* [len(ents) == 0]: the log is untouched and the result is the old
         last index.  The predicate does not have to be opened at all. *)
      subst ents. simpl in Hlen.
      rewrite bool_decide_eq_true_2; last word.
      wp_auto.
      wp_apply (wp_raftLog__lastIndex_at with "[$Hlog]") as "%li [Hlog %Hli]".
      iApply ("HΦ" $! li). rewrite app_nil_r. iFrame.
      iPureIntro. simpl. lia.
    - (* the batch is non-empty: [ents[0]] exists *)
      assert (∃ e0, ents !! 0%nat = Some e0) as [e0 He0].
      { destruct ents as [|x xs]; [done|]. by exists x. }
      assert (0 < length ents)%nat as Hpos
        by (apply lookup_lt_is_Some_1; eauto).
      rewrite bool_decide_eq_false_2; last word.
      wp_auto.
      (* [ents[0].Index] is one past the current last index *)
      assert (uint.Z e0.(raftpb.Entry.Index')
              = uint.Z prev.(raft.entryID.index') + Z.of_nat (length sents)
                + Z.of_nat (length uents) + 1)%Z as Hi0.
      { specialize (Hidx' (length sents + length uents)%nat e0).
        rewrite lookup_app_r in Hidx'; last lia.
        rewrite lookup_app_r in Hidx'; last lia.
        replace (length sents + length uents - length sents - length uents)%nat
          with 0%nat in Hidx' by lia.
        specialize (Hidx' He0). lia. }
      rewrite decide_True; last word.
      iDestruct (own_slice_elem_acc 0 e0 es dq ents with "Hes")
        as "[He0 Hesback]"; [ word | exact He0 | ].
      wp_auto.
      iDestruct ("Hesback" with "He0") as "Hes".
      rewrite list_insert_id //.
      (* the [Panicf]: [after] is the old last index, which is at least
         [committed] *)
      iNamed "Hlog".
      wp_auto.
      rewrite bool_decide_eq_false_2; last word.
      wp_auto.
      (* hand the [unstable] field to [truncateAndAppend] *)
      iDestruct (raftLog_split_unstable with "Hl") as "[Huf Hlback]".
      assert (uint.Z e0.(raftpb.Entry.Index')
              = uint.Z lv.(raft.raftLog.unstable').(raft.unstable.offset')
                + Z.of_nat (length uents))%Z as Hcont by word.
      wp_apply (wp_unstable__truncateAndAppend _ _ _ _ _ _ _ He0 Hcont
                  with "[$Huf $Huents $Huents_cap $Hes]")
        as "%sl (Huf & Huents & Huents_cap & Hes)".
      iDestruct ("Hlback" with "Huf") as "Hl".
      (* re-seal at the new split and read the new last index *)
      assert (Forall (λ e, e.(raftpb.Entry.Type') = EntryNormal)
                (sents ++ (uents ++ ents))) as Hnc2.
      { rewrite app_assoc. apply Forall_app. split; [ done | done ]. }
      assert (uint.Z prev.(raft.entryID.index') + Z.of_nat (length sents)
              + Z.of_nat (length (uents ++ ents)) + 1 < 2^64)%Z as Hnw2
        by (rewrite length_app; lia).
      assert (uint.Z lv.(raft.raftLog.committed')
              ≤ uint.Z prev.(raft.entryID.index') + Z.of_nat (length sents)
                + Z.of_nat (length (uents ++ ents)))%Z as Hcm2
        by (rewrite length_app; lia).
      iAssert (own_raftLog_at l prev sents (uents ++ ents))
        with "[Hl HStorage Huents Huents_cap]" as "Hlog".
      { rewrite /own_raftLog_at.
        iExists (lv <| raft.raftLog.unstable' :=
                   lv.(raft.raftLog.unstable')
                     <| raft.unstable.entries' := sl |> |>).
        iFrame "Hl". simpl. iFrame "∗#%". }
      wp_apply (wp_raftLog__lastIndex_at with "[$Hlog]") as "%li [Hlog %Hli]".
      iApply ("HΦ" $! li). iFrame.
      iPureIntro. rewrite length_app in Hli. lia.
  Qed.

End RaftLogAppendProof.
