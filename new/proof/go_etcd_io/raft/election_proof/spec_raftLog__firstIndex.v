Require Export New.proof.go_etcd_io.raft.election_proof.inv_raft_phys.

(** [l.firstIndex()]: one past the compaction boundary.

    The log comes back at the same state [ls], because [raftLog.term]
    calls this on itself and needs the entry list to come back unchanged --
    see [own_raftLog] in [inv_raftlog.v].

    The function ends in a [panic] on an error from [Storage].
    [wp_Logger__logf] deliberately does not cover the panicking methods, so
    this proof has to *reach* the [Storage] call with its precondition
    satisfied; that is the whole content of the lemma. *)
Definition wp_raftLog__firstIndex_body :=
  ∀ (ext : ffi_syntax) (ffi : ffi_model) (ffi_interp0 : ffi_interp ffi)
    (Σ : gFunctors) (hG : heapGS Σ) (ffi_semantics0 : ffi_semantics ext ffi)
    (sem : go.Semantics) (package_sem : raft.Assumptions)
    (l : loc) (ls : logstate.t),
  ls.(logstate.page) = None →
  {{{ is_pkg_init raft ∗ "Hlog" ∷ own_raftLog l ls }}}
    l @! (go.PointerType raft.raftLog) @! "firstIndex" #()
  {{{ (i : w64), RET #i;
      own_raftLog l ls ∗
      ⌜ (uint.Z i = uint.Z ls.(logstate.prev).(raft.entryID.index') + 1)%Z ⌝ }}}.

Module Type RAFTLOG__FIRSTINDEX.
  Parameter wp_raftLog__firstIndex : wp_raftLog__firstIndex_body.
  Arguments wp_raftLog__firstIndex {_ _ _ _ _ _ _ _}.
End RAFTLOG__FIRSTINDEX.
