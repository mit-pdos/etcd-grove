(** * Link: [raft.raft__send_vote]

    [raft__send_vote] is proved, so this file carries no [Axiom]. *)

Require Export New.proof.go_etcd_io.raft.v3_proof.election.proof_raft__send_vote.

Module SendVotePostulates : SEND_VOTE_POSTULATES.
End SendVotePostulates.

Module SendVote := SendVoteProof SendVotePostulates.

(** Implicits are not inferred through a folded [_body], and an [Arguments]
    inside the [Module Type] does not survive functor application. *)
Arguments SendVote.wp_raft__send_vote {_ _ _ _ _ _ _ _}.
