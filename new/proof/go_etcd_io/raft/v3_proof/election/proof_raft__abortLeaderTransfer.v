Require Export New.proof.go_etcd_io.raft.v3_proof.election.postulates_raft__abortLeaderTransfer.

Module RaftAbortLeaderTransferProof (P : RAFT__ABORTLEADERTRANSFER_POSTULATES) : RAFT__ABORTLEADERTRANSFER.

  Lemma wp_raft__abortLeaderTransfer : wp_raft__abortLeaderTransfer_body.
  Proof.
    intros_ambient.
    intros cfg r id s.
    (* [leadTransferee := None]; [own_raft_phys] already says it is [0]
       (no leader transfer is in scope), so nothing abstract moves. *)
    wp_start as "Hphys". iNamed "Hphys". wp_auto.
    iApply "HΦ".
    iApply (own_raft_phys_intro with
      "Hr Hlogger Hprs Htrk Hlog Hmsgs Hmsgs_cap HmsgsAA HmsgsAA_cap Hmisc"); done.
  Qed.

End RaftAbortLeaderTransferProof.
