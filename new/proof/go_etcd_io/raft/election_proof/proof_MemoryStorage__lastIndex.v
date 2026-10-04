Require Export New.proof.go_etcd_io.raft.election_proof.postulates_MemoryStorage__lastIndex.

Module MemoryStorageLastIndexProof (P : MEMORYSTORAGE__LASTINDEX_POSTULATES) : MEMORYSTORAGE__LASTINDEX.
Import P.

  (** [ents[0].Index + len(ents) - 1], read through the dummy entry.  The
      slice is read-only ([↦*□]), so the element access is the one
      [limitSize] uses ([own_slice_elem_acc]) and the entry is handed back
      at once.  The sum does not wrap: [Hb]. *)
  Lemma wp_MemoryStorage__lastIndex : wp_MemoryStorage__lastIndex_body.
  Proof.
    intros_ambient.
    intros ms prev ents ss Hb.
    wp_start as "H". iNamed "H". iNamed "Hf".
    wp_auto.
    iDestruct (own_slice_len with "Hents") as %[Hlen Hlen'].
    simpl in Hlen.
    iDestruct (own_slice_elem_acc 0 dummy with "Hents") as "[He Hback]"; [lia|done|].
    case_decide as Hdec; last first.
    { exfalso. apply Hdec. clear Hdec Hdummy. word. }
    clear Hdec.
    wp_auto.
    iDestruct ("Hback" with "He") as "Hents".
    iApply "HΦ".
    iSplit.
    - iPureIntro. destruct Hdummy as [Hd _]. rewrite Hd. word.
    - iFrame "∗%".
  Qed.

End MemoryStorageLastIndexProof.
