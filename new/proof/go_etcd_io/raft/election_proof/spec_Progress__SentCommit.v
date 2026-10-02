Require Export New.proof.go_etcd_io.raft.election_proof.inv_raft_phys.

(** [pr.SentCommit(commit)] is one field assignment
    ([Progress__SentCommitⁱᵐᵖˡ], new/code/go_etcd_io/raft/v3/tracker.v:357):
    [pr.sentCommit = commit] -- [progress_sent_commit p commit] ([defs.v]).
    The field is read by [Progress.CanBumpCommit]. *)
Definition wp_Progress__SentCommit_body :=
  ∀ (ext : ffi_syntax) (ffi : ffi_model) (ffi_interp0 : ffi_interp ffi)
    (Σ : gFunctors) (hG : heapGS Σ) (ffi_semantics0 : ffi_semantics ext ffi)
    (sem : go.Semantics) (package_sem : raft.Assumptions)
    (pr : loc) (p : progress.t) (commit : w64),
  {{{ is_pkg_init tracker ∗ "Hpr" ∷ own_Progress pr p }}}
    pr @! (go.PointerType tracker.Progress) @! "SentCommit" #commit
  {{{ RET #(); own_Progress pr (progress_sent_commit p commit) }}}.

Module Type PROGRESS__SENTCOMMIT.
  Parameter wp_Progress__SentCommit : wp_Progress__SentCommit_body.
  Arguments wp_Progress__SentCommit {_ _ _ _ _ _ _ _}.
End PROGRESS__SENTCOMMIT.
