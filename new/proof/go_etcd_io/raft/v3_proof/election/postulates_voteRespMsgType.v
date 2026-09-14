(** * Postulates: [raft.voteRespMsgType]

    Include only *direct* callees here, never another [_POSTULATES] -- a
    transitive include would re-declare a label another branch already
    contributes, and [Include] rejects that. *)

Require Export New.proof.go_etcd_io.raft.v3_proof.election.spec_voteRespMsgType.

(** [voteRespMsgType] is a pure switch on the message type; it calls nothing. *)
Module Type VOTERESPMSGTYPE_POSTULATES.
End VOTERESPMSGTYPE_POSTULATES.
