Require Export New.proof.go_etcd_io.raft.election_proof.postulates_payloadSize.

Module PayloadSizeProof (P : PAYLOADSIZE_POSTULATES) : PAYLOADSIZE.

  Lemma wp_payloadSize : wp_payloadSize_body.
  Proof.
    intros_ambient.
    intros e.
    wp_start as "_". wp_auto. by iApply "HΦ".
  Qed.

End PayloadSizeProof.
