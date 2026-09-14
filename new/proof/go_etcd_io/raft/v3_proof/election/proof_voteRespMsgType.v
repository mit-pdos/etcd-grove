(** * Proof: [raft.voteRespMsgType] against its spec

    Opaquely ascribed ([: VOTERESPMSGTYPE]), so the proof term is sealed and
    callers can depend on nothing but the spec. *)

Require Export New.proof.go_etcd_io.raft.v3_proof.election.postulates_voteRespMsgType.

Module VoteRespMsgTypeProof (P : VOTERESPMSGTYPE_POSTULATES) : VOTERESPMSGTYPE.

  (** The context binders arrive by [intros] rather than [Context]: the
      lemma's type is closed, so there are no section variables to discharge
      and no [Collection W] is needed. *)
  Lemma wp_voteRespMsgType : wp_voteRespMsgType_body.
  Proof.
    intros ?????? sem package_sem t Ht.
    wp_start as "_". wp_auto.
    rewrite Ht /MsgVote bool_decide_eq_true_2 //. wp_auto.
    by iApply "HΦ".
  Qed.

End VoteRespMsgTypeProof.
