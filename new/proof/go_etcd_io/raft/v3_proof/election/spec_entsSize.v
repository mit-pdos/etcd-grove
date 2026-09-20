Require Export New.proof.go_etcd_io.raft.v3_proof.election.inv_raft_phys.

(** [entsSize(ents)]: the summed encoded size of the entries.  The value
    is unspecified, since [Entry.Size] (pointer receiver) is ([spec_Entry__Size.v]);
    [raftLog.slice] only compares it against [maxSize] to decide whether to
    append the unstable part of a page, and either answer is fine. *)
Definition wp_entsSize_body :=
  ∀ (ext : ffi_syntax) (ffi : ffi_model) (ffi_interp0 : ffi_interp ffi)
    (Σ : gFunctors) (hG : heapGS Σ) (ffi_semantics0 : ffi_semantics ext ffi)
    (sem : go.Semantics) (package_sem : raft.Assumptions)
    (s : slice.t) (es : list raftpb.Entry.t) (dq : dfrac),
  {{{ is_pkg_init raft ∗ "Hs" ∷ s ↦*{dq} es }}}
    @! raft.entsSize #s
  {{{ (n : w64), RET #n; s ↦*{dq} es }}}.

Module Type ENTSSIZE.
  Parameter wp_entsSize : wp_entsSize_body.
  Arguments wp_entsSize {_ _ _ _ _ _ _ _}.
End ENTSSIZE.
