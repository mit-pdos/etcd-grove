Require Export New.proof.go_etcd_io.raft.election_proof.postulates_logSliceFromMsgApp.

Module LogSliceFromMsgAppProof (P : LOGSLICEFROMMSGAPP_POSTULATES) : LOGSLICEFROMMSGAPP.

  Lemma wp_logSliceFromMsgApp : wp_logSliceFromMsgApp_body.
  Proof.
    intros_ambient.
    intros p dq m.
    wp_start as "Hm". wp_auto.
    iApply "HΦ". iFrame.
  Qed.

End LogSliceFromMsgAppProof.
