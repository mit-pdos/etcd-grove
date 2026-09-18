Require Export New.proof.go_etcd_io.raft.v3_proof.election.postulates_traceSendMessage.

Module TraceSendMessageProof (P : TRACESENDMESSAGE_POSTULATES) : TRACESENDMESSAGE.

  Lemma wp_traceSendMessage : wp_traceSendMessage_body.
  Proof.
    intros_ambient.
    intros r mp rs ro pri.
   wp_start as "Hm". by iApply "HΦ".
  Qed.

End TraceSendMessageProof.
