Require Export New.proof.go_etcd_io.raft.election_proof.postulates_raftLog__appliedTo.

Module RaftLogAppliedToProof (P : RAFTLOG__APPLIEDTO_POSTULATES) : RAFTLOG__APPLIEDTO.

  Lemma wp_raftLog__appliedTo : wp_raftLog__appliedTo_body.
  Proof.
    intros_ambient.
    intros l ls i size Hi.
    destruct ls as [prev sents uents lcm lap snap]; logstate_simpl.
    wp_start as "Hlog".
    iDestruct (own_raftLog_unfold with "Hlog") as (lv) "(Hl & %Hcm & %Hap & Hcore)".
    logstate_simpl.
    wp_auto.
    rewrite bool_decide_eq_false_2; last (subst; lia). wp_auto.
    rewrite bool_decide_eq_false_2; last (subst; lia). wp_auto.
    wp_apply wp_max2_uint64. try wp_auto.
    case_bool_decide; try wp_auto.
    all: iApply "HΦ"; iEval (rewrite /own_raftLog_core /=) in "Hcore";
      iDestruct "Hcore" as (sprev stored ss) "Hcore"; iNamed "Hcore";
      reseal_raftLog.
    all: simpl; subst; first [lia | (intros Hn; specialize (Hpapplied Hn); lia)].
  Qed.

End RaftLogAppliedToProof.
