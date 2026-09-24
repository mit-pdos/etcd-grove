Require Export New.proof.go_etcd_io.raft.election_proof.postulates_assertConfStatesEquivalent.

Module AssertConfStatesEquivalentProof (P : ASSERTCONFSTATESEQUIVALENT_POSTULATES) : ASSERTCONFSTATESEQUIVALENT.
Import P.

  Lemma wp_assertConfStatesEquivalent : wp_assertConfStatesEquivalent_body.
  Proof.
    intros_ambient.
    intros l cs1 cs2 v1 v2 dq1 dq2 Hperm H1 H2 H3 H4 H5 H6 Hal.
    wp_start as "[H1 H2]". wp_auto.
    wp_apply (P.wp_ConfState__Equivalent _ _ _ _ _ _ _ Hperm H1 H2 H3 H4 H5 H6 Hal
                with "[$cs1 $H1 $H2]") as "(_ & H1 & H2)".
    try wp_auto. iApply "HΦ". iFrame.
  Qed.

End AssertConfStatesEquivalentProof.
