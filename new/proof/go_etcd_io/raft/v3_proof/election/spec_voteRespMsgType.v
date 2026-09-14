(** * Spec: [raft.voteRespMsgType]

    The single place this function's Hoare triple is written down.  The body
    carries all of its own binders, so the [Parameter] below is a bare
    reference to it -- there is no second copy of the binder list to drift. *)

Require Export New.proof.go_etcd_io.raft.v3_proof.election.defs.

(** [voteRespMsgType] maps a vote request to its response type. *)
Definition wp_voteRespMsgType_body :=
  ∀ (ext : ffi_syntax) (ffi : ffi_model) (ffi_interp0 : ffi_interp ffi)
    (Σ : gFunctors) (hG : heapGS Σ) (ffi_semantics0 : ffi_semantics ext ffi)
    (sem : go.Semantics) (package_sem : raft.Assumptions)
    (t : w32),
  t = MsgVote →
  {{{ is_pkg_init raft }}}
    @! raft.voteRespMsgType #t
  {{{ RET #MsgVoteResp; True }}}.

Module Type VOTERESPMSGTYPE.
  Parameter wp_voteRespMsgType : wp_voteRespMsgType_body.
End VOTERESPMSGTYPE.
