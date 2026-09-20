Require Export New.proof.go_etcd_io.raft.v3_proof.election.inv_raft_phys.

(** [pr.SentCommit(commit)] is one field assignment
    ([Progress__SentCommitⁱᵐᵖˡ], new/code/go_etcd_io/raft/v3/tracker.v:357):
    [pr.sentCommit = commit].  The field is read only by
    [Progress.CanBumpCommit], which nothing on the election path calls. *)
Definition wp_Progress__SentCommit_body :=
  ∀ (ext : ffi_syntax) (ffi : ffi_model) (ffi_interp0 : ffi_interp ffi)
    (Σ : gFunctors) (hG : heapGS Σ) (ffi_semantics0 : ffi_semantics ext ffi)
    (sem : go.Semantics) (package_sem : raft.Assumptions)
    (pr : loc) (pv : tracker.Progress.t) (iv : tracker.Inflights.t)
    (commit : w64),
  {{{ is_pkg_init tracker ∗ "Hpr" ∷ own_progress_at pr pv iv }}}
    pr @! (go.PointerType tracker.Progress) @! "SentCommit" #commit
  {{{ RET #();
      own_progress_at pr (pv <| tracker.Progress.sentCommit' := commit |>) iv }}}.

Module Type PROGRESS__SENTCOMMIT.
  Parameter wp_Progress__SentCommit : wp_Progress__SentCommit_body.
  Arguments wp_Progress__SentCommit {_ _ _ _ _ _ _ _}.
End PROGRESS__SENTCOMMIT.
