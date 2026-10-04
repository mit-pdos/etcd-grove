Require Export New.proof.go_etcd_io.raft.election_proof.defs.

(** [voteRespMsgType] maps a vote request to its response type: [MsgVote]
    to [MsgVoteResp], and (since 2026-10-04) [MsgPreVote] to
    [MsgPreVoteResp].  Any other type panics.  Stated as a relation between
    [t] and the result [r], so that a caller names the result it expects. *)
Definition wp_voteRespMsgType_body :=
  ∀ (ext : ffi_syntax) (ffi : ffi_model) (ffi_interp0 : ffi_interp ffi)
    (Σ : gFunctors) (hG : heapGS Σ) (ffi_semantics0 : ffi_semantics ext ffi)
    (sem : go.Semantics) (package_sem : raft.Assumptions)
    (t r : w32),
  (t = MsgVote ∧ r = MsgVoteResp) ∨ (t = MsgPreVote ∧ r = MsgPreVoteResp) →
  {{{ is_pkg_init raft }}}
    @! raft.voteRespMsgType #t
  {{{ RET #r; True }}}.

Module Type VOTERESPMSGTYPE.
  Parameter wp_voteRespMsgType : wp_voteRespMsgType_body.
  Arguments wp_voteRespMsgType {_ _ _ _ _ _ _ _}.
End VOTERESPMSGTYPE.
