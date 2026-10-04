Require Export New.proof.go_etcd_io.raft.election_proof.postulates_readOnly__addRequest.

Module ReadOnlyAddRequestProof (P : READONLY__ADDREQUEST_POSTULATES)
  : READONLY__ADDREQUEST.

  Lemma wp_readOnly__addRequest : wp_readOnly__addRequest_body.
  Proof.
    intros_ambient.
    intros ro r commitIndex req ents.
    wp_start as "Hown". iNamed "Hown". iNamed "Hown".
    wp_auto.
    wp_alloc req_ptr as "Hreq".
    iPersist "Hreq".
    wp_auto.
    wp_apply wp_slice_literal. iSplitR; [done|]. iIntros "% [Hsl _]". wp_auto.
    replace (sint.nat (W64 0)) with (O) by done.
    rewrite /go.array_literal_size /= /Z.max /= /Z.add /=.
    wp_apply (wp_slice_append_persistent with "[$Hucr_cap $Hucr $Hsl]") as "%s' (Hs' & Hcap' & _)".
    iApply "HΦ".
    iExists (rov <| raft.readOnly.unconfirmedReads' := s' |>), (ptrs ++ [req_ptr]).
    iFrame "Hro Hacks Hs' Hcap'".
    iSplit; first (iPureIntro; exact Hro_safe).
    iSplit; first (iPureIntro; exact Hro_conf).
    rewrite /readonly_add /=.
    iApply (big_sepL2_app with "Hreqs").
    rewrite big_sepL2_singleton.
    iExists _. iFrame "Hreq Hents". done.
  Qed.

End ReadOnlyAddRequestProof.
