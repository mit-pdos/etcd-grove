(** * Proof: [raft.raft__Step_MsgVoteResp] against its spec

    Opaquely ascribed, so the proof term is sealed: callers can depend on
    nothing but the spec.  The binders arrive by [intros] rather than
    [Context] -- the lemma's type is closed, so there are no section variables
    to discharge and no [Collection W] is needed. *)

Require Export New.proof.go_etcd_io.raft.v3_proof.election.postulates_raft__Step_MsgVoteResp.

Module StepMsgVoteRespProof (P : STEP_MSGVOTERESP_POSTULATES) : STEP_MSGVOTERESP.

  Lemma wp_raft__Step_MsgVoteResp : wp_raft__Step_MsgVoteResp_body.
  Proof.
  Admitted.

End StepMsgVoteRespProof.
