Require Export New.proof.go_etcd_io.raft.v3_proof.election.proof_voteRespMsgType.

Module VoteRespMsgTypePostulates : VOTERESPMSGTYPE_POSTULATES.
End VoteRespMsgTypePostulates.

Module VoteRespMsgType := VoteRespMsgTypeProof VoteRespMsgTypePostulates.

(* Implicits do not survive a folded [_body]; see notes/gotchas.md. *)
Arguments VoteRespMsgType.wp_voteRespMsgType {_ _ _ _ _ _ _ _}.
