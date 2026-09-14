(** * Link: [raft.voteRespMsgType]

    [voteRespMsgType] is proved, so this file carries no [Axiom]. *)

Require Export New.proof.go_etcd_io.raft.v3_proof.election.proof_voteRespMsgType.

Module VoteRespMsgTypePostulates : VOTERESPMSGTYPE_POSTULATES.
End VoteRespMsgTypePostulates.

Module VoteRespMsgType := VoteRespMsgTypeProof VoteRespMsgTypePostulates.

(** Implicits are not inferred through a folded [_body], and the [Module Type]
    declaration does not survive functor application, so restore them here. *)
Arguments VoteRespMsgType.wp_voteRespMsgType {_ _ _ _ _ _ _ _} _ _.
