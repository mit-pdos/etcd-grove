Require Export New.proof.go_etcd_io.raft.election_proof.postulates_voteRespMsgType.

Module VoteRespMsgTypeProof (P : VOTERESPMSGTYPE_POSTULATES) : VOTERESPMSGTYPE.

  Lemma wp_voteRespMsgType : wp_voteRespMsgType_body.
  Proof.
    intros_ambient.
    intros t Ht.
    wp_start as "_". wp_auto.
    rewrite Ht /MsgVote bool_decide_eq_true_2 //. wp_auto.
    by iApply "HΦ".
  Qed.

End VoteRespMsgTypeProof.
