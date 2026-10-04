Require Export New.proof.go_etcd_io.raft.election_proof.postulates_voteRespMsgType.

Module VoteRespMsgTypeProof (P : VOTERESPMSGTYPE_POSTULATES) : VOTERESPMSGTYPE.

  Lemma wp_voteRespMsgType : wp_voteRespMsgType_body.
  Proof.
    intros_ambient.
    intros t r Ht.
    wp_start as "_". wp_auto.
    destruct Ht as [[-> ->]|[-> ->]].
    - rewrite bool_decide_eq_true_2 //. wp_auto.
      by iApply "HΦ".
    - rewrite bool_decide_eq_false_2; last (rewrite /MsgPreVote; w32_ne). wp_auto.
      by iApply "HΦ".
  Qed.

End VoteRespMsgTypeProof.
