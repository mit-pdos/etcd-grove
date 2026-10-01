Require Export New.proof.go_etcd_io.raft.election_proof.inv_raft_phys.
Require Export New.proof.go_etcd_io.raft.election_proof.plog.

(** [l.matchTerm(id)]: whether the log has term [id.term] at [id.index]
    -- [plog_matches] ([plog.v]) of the log the protocol sees.

    The body ([raftLog__matchTermⁱᵐᵖˡ], new/code/go_etcd_io/raft/v3.v:1159)
    is [t, err := l.term(id.index); if err != nil { return false }; return
    t == id.term].  [term]'s spec makes both halves exact: the error is
    non-[nil] exactly when [id.index] is outside [[prev.index, last]], where
    [plog_term_at] is [None], and otherwise [t] is [plog_term_at]'s value.
    No premise, no panic. *)
Definition wp_raftLog__matchTerm_body :=
  ∀ (ext : ffi_syntax) (ffi : ffi_model) (ffi_interp0 : ffi_interp ffi)
    (Σ : gFunctors) (hG : heapGS Σ) (ffi_semantics0 : ffi_semantics ext ffi)
    (sem : go.Semantics) (package_sem : raft.Assumptions)
    (l : loc) (ls : logstate.t) (id : raft.entryID.t),
  {{{ is_pkg_init raft ∗ "Hlog" ∷ own_raftLog l ls }}}
    l @! (go.PointerType raft.raftLog) @! "matchTerm" #id
  {{{ (b : bool), RET #b;
      own_raftLog l ls ∗
      ⌜ b = bool_decide (plog_matches ls.(logstate.prev)
                           (ls.(logstate.sents) ++ ls.(logstate.uents)) id) ⌝ }}}.

Module Type RAFTLOG__MATCHTERM.
  Parameter wp_raftLog__matchTerm : wp_raftLog__matchTerm_body.
  Arguments wp_raftLog__matchTerm {_ _ _ _ _ _ _ _}.
End RAFTLOG__MATCHTERM.
