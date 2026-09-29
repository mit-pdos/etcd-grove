Require Export New.proof.go_etcd_io.raft.election_proof.inv_raft_phys.

(** [l.lastIndex()]: the index of the last entry.

    Stated at the log's state [ls], and the postcondition pins the value:
    [prev.index + |sents| + |uents|].  That equation is what [term]'s and
    [lastEntryID]'s proofs need in order to satisfy [Storage.Term]'s range
    premise.

    Both branches (the [unstable] one and the [storage] fallback) have to
    agree, which is what the [unstable.offset] conjunct of [own_raftLog]
    buys.  Like [firstIndex], the [Panicf] path has to be shown unreachable
    rather than assumed away. *)
Definition wp_raftLog__lastIndex_body :=
  ∀ (ext : ffi_syntax) (ffi : ffi_model) (ffi_interp0 : ffi_interp ffi)
    (Σ : gFunctors) (hG : heapGS Σ) (ffi_semantics0 : ffi_semantics ext ffi)
    (sem : go.Semantics) (package_sem : raft.Assumptions)
    (l : loc) (ls : logstate.t),
  {{{ is_pkg_init raft ∗ "Hlog" ∷ own_raftLog l ls }}}
    l @! (go.PointerType raft.raftLog) @! "lastIndex" #()
  {{{ (i : w64), RET #i;
      own_raftLog l ls ∗
      ⌜ (uint.Z i = uint.Z ls.(logstate.prev).(raft.entryID.index') + Z.of_nat (length ls.(logstate.sents))
                    + Z.of_nat (length ls.(logstate.uents)))%Z ⌝ }}}.

Module Type RAFTLOG__LASTINDEX.
  Parameter wp_raftLog__lastIndex : wp_raftLog__lastIndex_body.
  Arguments wp_raftLog__lastIndex {_ _ _ _ _ _ _ _}.
End RAFTLOG__LASTINDEX.
