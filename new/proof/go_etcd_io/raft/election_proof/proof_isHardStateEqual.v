Require Export New.proof.go_etcd_io.raft.election_proof.postulates_isHardStateEqual.

Module IsHardStateEqualProof (P : ISHARDSTATEEQUAL_POSTULATES) : ISHARDSTATEEQUAL.

  Lemma wp_isHardStateEqual : wp_isHardStateEqual_body.
  Proof.
    intros_ambient.
    intros a b.
    wp_start as "_". wp_auto.
    destruct a as [t1 v1 c1], b as [t2 v2 c2]; simpl.
    destruct (decide (t1 = t2)) as [<-|H1];
      [rewrite (bool_decide_eq_true_2 (t1 = t1)) //
      |rewrite (bool_decide_eq_false_2 (t1 = t2)) //]; wp_auto;
    [destruct (decide (v1 = v2)) as [<-|H2];
      [rewrite (bool_decide_eq_true_2 (v1 = v1)) //
      |rewrite (bool_decide_eq_false_2 (v1 = v2)) //]; wp_auto| ];
    iSpecialize ("HΦ" with "[//]"); iExactEq "HΦ"; do 2 f_equal;
    repeat case_bool_decide; naive_solver.
  Qed.

End IsHardStateEqualProof.
