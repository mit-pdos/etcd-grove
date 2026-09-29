Require Export New.proof.go_etcd_io.raft.election_proof.postulates_raftLog__isUpToDate.

Module RaftLogIsUpToDateProof (P : RAFTLOG__ISUPTODATE_POSTULATES) : RAFTLOG__ISUPTODATE.
Import P.

  Lemma wp_raftLog__isUpToDate : wp_raftLog__isUpToDate_body.
  Proof.
    intros_ambient.
    intros l e ls.
    wp_start as "Hlog". wp_auto.
    wp_apply (wp_raftLog__lastEntryID _ _ with "[$Hlog]") as "%our Hlog".
    repeat (case_bool_decide; try wp_auto).
    all: iApply "HΦ"; iFrame.
  Qed.

End RaftLogIsUpToDateProof.
