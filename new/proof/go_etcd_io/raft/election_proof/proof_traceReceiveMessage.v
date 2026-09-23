Require Export New.proof.go_etcd_io.raft.election_proof.postulates_traceReceiveMessage.

Module TraceReceiveMessageProof (P : TRACERECEIVEMESSAGE_POSTULATES) : TRACERECEIVEMESSAGE.

  Lemma wp_traceReceiveMessage : wp_traceReceiveMessage_body.
  Proof.
    intros_ambient.
    intros r mp.
    wp_start. by iApply "HΦ".
  Qed.

End TraceReceiveMessageProof.
