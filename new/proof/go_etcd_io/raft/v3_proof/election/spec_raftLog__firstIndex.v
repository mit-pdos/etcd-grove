Require Export New.proof.go_etcd_io.raft.v3_proof.election.inv_raft_phys.

(** [l.firstIndex()]: one past the compaction boundary.

    Stated at a fixed split ([own_raftLog_at], hence the [_at] in the name),
    because [raftLog.term] calls this on itself and needs the split to come
    back unchanged -- see [own_raftLog_at] in [inv_raftlog.v].  A caller
    holding only [own_raftLog] gets there with [own_raftLog_acc].

    The function ends in a [panic] on an error from [Storage].
    [wp_Logger__logf] deliberately does not cover the panicking methods, so
    this proof has to *reach* the [Storage] call with its precondition
    satisfied; that is the whole content of the lemma. *)
Definition wp_raftLog__firstIndex_at_body :=
  ∀ (ext : ffi_syntax) (ffi : ffi_model) (ffi_interp0 : ffi_interp ffi)
    (Σ : gFunctors) (hG : heapGS Σ) (ffi_semantics0 : ffi_semantics ext ffi)
    (sem : go.Semantics) (package_sem : raft.Assumptions)
    (l : loc) prev sents uents,
  {{{ is_pkg_init raft ∗ "Hlog" ∷ own_raftLog_at l prev sents uents }}}
    l @! (go.PointerType raft.raftLog) @! "firstIndex" #()
  {{{ (i : w64), RET #i;
      own_raftLog_at l prev sents uents ∗
      ⌜ (uint.Z i = uint.Z prev.(raft.entryID.index') + 1)%Z ⌝ }}}.

Module Type RAFTLOG__FIRSTINDEX.
  Parameter wp_raftLog__firstIndex_at : wp_raftLog__firstIndex_at_body.
  Arguments wp_raftLog__firstIndex_at {_ _ _ _ _ _ _ _}.
End RAFTLOG__FIRSTINDEX.
