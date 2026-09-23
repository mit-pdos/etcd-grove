Require Export New.proof.go_etcd_io.raft.election_proof.postulates_traceSendMessage.

Module TraceSendMessageProof (P : TRACESENDMESSAGE_POSTULATES) : TRACESENDMESSAGE.

  Lemma wp_traceSendMessage : wp_traceSendMessage_body.
  Proof.
    intros_ambient.
    intros r mp.
    wp_start. by iApply "HΦ".
  Qed.

End TraceSendMessageProof.
