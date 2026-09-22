Require Export New.proof.go_etcd_io.raft.election_proof.postulates_raft__abortLeaderTransfer.

Module RaftAbortLeaderTransferProof (P : RAFT__ABORTLEADERTRANSFER_POSTULATES) : RAFT__ABORTLEADERTRANSFER.

  Lemma wp_raft__abortLeaderTransfer : wp_raft__abortLeaderTransfer_body.
  Proof.
    intros_ambient.
    intros r rv.
   wp_start as "Hr". wp_auto. by iApply "HΦ".
  Qed.

End RaftAbortLeaderTransferProof.
