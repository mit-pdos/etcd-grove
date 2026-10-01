Require Export New.proof.go_etcd_io.raft.election_proof.postulates_raftLog__isUpToDate.

Module RaftLogIsUpToDateProof (P : RAFTLOG__ISUPTODATE_POSTULATES) : RAFTLOG__ISUPTODATE.
Import P.

  Lemma wp_raftLog__isUpToDate : wp_raftLog__isUpToDate_body.
  Proof.
    intros_ambient.
    intros l e ls.
    wp_start as "Hlog". wp_auto.
    wp_apply (wp_raftLog__lastEntryID _ _ with "[$Hlog]") as "%our [Hlog %Hour]".
    repeat (case_bool_decide; try wp_auto).
    all: iApply "HΦ"; iFrame; iPureIntro; rewrite /plog_up_to_date -Hour; symmetry.
    all: first [ apply bool_decide_eq_true_2 | apply bool_decide_eq_false_2 ].
    all: first [ (left; word)
               | (right; split; [congruence | word])
               | (intros [Hc|[Hc1 Hc2]]; first [word | congruence]) ].
  Qed.

End RaftLogIsUpToDateProof.
