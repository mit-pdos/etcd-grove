Require Export New.proof.go_etcd_io.raft.election_proof.postulates_Config__validate.

Module ConfigValidateProof (P : CONFIG__VALIDATE_POSTULATES) : CONFIG__VALIDATE.
Import P.

  Lemma wp_Config__validate : wp_Config__validate_body.
  Proof.
    intros_ambient.
    intros c cv Hvalid.
    wp_start as "Hc".
    destruct Hvalid as (Hid & Hid1 & Hid2 & Hticks & Hst & Hinfl & Hib & Hlog & Hro).
    wp_auto.
    rewrite bool_decide_eq_false_2 //. wp_auto.
    wp_apply P.wp_IsLocalMsgTarget.
    rewrite bool_decide_eq_false_2; [|naive_solver]. wp_auto.
    rewrite bool_decide_eq_false_2; [|word]. wp_auto.
    rewrite bool_decide_eq_false_2; [|word]. wp_auto.
    destruct cv.(raft.Config.Storage') as [?|] eqn:Hstv; [|congruence].
    wp_auto.
    (* the three defaults and the two remaining checks *)
    case_bool_decide; wp_auto.
    all: case_bool_decide; wp_auto.
    all: rewrite bool_decide_eq_false_2; [|word]; wp_auto.
    all: case_bool_decide as Hib0; wp_auto;
      [| rewrite bool_decide_eq_false_2; [|destruct Hib; [done|word]]; wp_auto].
    all: destruct cv.(raft.Config.Logger') as [?|] eqn:Hlogv; [|congruence].
    all: wp_auto.
    all: case_bool_decide as Hro1; wp_auto;
      [ destruct Hro as [Hro|Hcq]; [rewrite Hro in Hro1; discriminate|];
        rewrite Hcq; wp_auto | ].
    all: iApply "HΦ"; iFrame "Hc"; iPureIntro; rewrite /config_preserved /=;
      split_and!; done.
  Qed.

End ConfigValidateProof.
