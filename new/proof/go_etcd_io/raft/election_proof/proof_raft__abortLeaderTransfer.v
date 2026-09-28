Require Export New.proof.go_etcd_io.raft.election_proof.postulates_raft__abortLeaderTransfer.

Module RaftAbortLeaderTransferProof (P : RAFT__ABORTLEADERTRANSFER_POSTULATES) : RAFT__ABORTLEADERTRANSFER.

  Lemma wp_raft__abortLeaderTransfer : wp_raft__abortLeaderTransfer_body.
  Proof.
    intros_ambient.
    intros cfg r id s.
    (* [leadTransferee := None]; [own_raft_phys] already says it is [0]
       (no leader transfer is in scope), so nothing abstract moves. *)
    wp_start as "Hphys". wp_auto.
    wp_apply (wp_raft_store_leadTransferee with "Hphys") as "Hphys".
    iApply "HΦ". iFrame.
  Qed.

End RaftAbortLeaderTransferProof.
