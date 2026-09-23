Require Export New.proof.go_etcd_io.raft.election_proof.postulates_raft__sendAppend.

Module RaftSendAppendProof (P : RAFT__SENDAPPEND_POSTULATES) : RAFT__SENDAPPEND.
Import P.

  Lemma wp_raft__sendAppend : wp_raft__sendAppend_body.
  Proof.
    intros_ambient.
    intros cfg r id s to Hto Hcfg Hlent.
    wp_start as "Hphys". wp_auto.
    wp_apply (wp_raft__maybeSendAppend _ _ _ _ _ true Hto Hcfg Hlent with "[$Hphys]")
      as "%b %ms [Hphys %Hms]".
    try wp_auto.
    iApply ("HΦ" $! ms). by iFrame.
  Qed.

End RaftSendAppendProof.
