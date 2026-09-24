Require Export New.proof.go_etcd_io.raft.election_proof.postulates_IsLocalMsgTarget.

Module IsLocalMsgTargetProof (P : ISLOCALMSGTARGET_POSTULATES) : ISLOCALMSGTARGET.

  Lemma wp_IsLocalMsgTarget : wp_IsLocalMsgTarget_body.
  Proof.
    intros_ambient.
    intros id.
    wp_start as "_". wp_auto.
    rewrite /raft.LocalApplyThread.
    destruct (decide (id = W64 18446744073709551615)) as [->|H1];
      [rewrite (bool_decide_eq_true_2 (W64 18446744073709551615 = W64 18446744073709551615)) //
      | rewrite (bool_decide_eq_false_2 (id = W64 18446744073709551615)) //];
      wp_auto;
      iSpecialize ("HΦ" with "[//]"); iExactEq "HΦ"; do 2 f_equal;
      repeat case_bool_decide; naive_solver.
  Qed.

End IsLocalMsgTargetProof.
