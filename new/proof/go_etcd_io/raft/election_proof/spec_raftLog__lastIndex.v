Require Export New.proof.go_etcd_io.raft.election_proof.inv_raft_phys.

(** [l.lastIndex()]: the index of the last entry.

    Stated at a fixed split ([_at]), and the postcondition pins the value:
    [prev.index + |sents| + |uents|].  That equation is what [term]'s and
    [lastEntryID]'s proofs need in order to satisfy [Storage.Term]'s range
    premise, so the weak form -- precondition and postcondition both just
    [own_raftLog l] -- is *not* enough and is not offered.  A caller holding
    only [own_raftLog] opens it with [own_raftLog_acc] ([inv_raftlog.v]).

    Both branches (the [unstable] one and the [storage] fallback) have to
    agree, which is what the [unstable.offset] conjunct of [own_raftLog_at]
    buys.  Like [firstIndex], the [Panicf] path has to be shown unreachable
    rather than assumed away. *)
Definition wp_raftLog__lastIndex_at_body :=
  ∀ (ext : ffi_syntax) (ffi : ffi_model) (ffi_interp0 : ffi_interp ffi)
    (Σ : gFunctors) (hG : heapGS Σ) (ffi_semantics0 : ffi_semantics ext ffi)
    (sem : go.Semantics) (package_sem : raft.Assumptions)
    (l : loc) prev sents uents,
  {{{ is_pkg_init raft ∗ "Hlog" ∷ own_raftLog_at l prev sents uents }}}
    l @! (go.PointerType raft.raftLog) @! "lastIndex" #()
  {{{ (i : w64), RET #i;
      own_raftLog_at l prev sents uents ∗
      ⌜ (uint.Z i = uint.Z prev.(raft.entryID.index') + Z.of_nat (length sents)
                    + Z.of_nat (length uents))%Z ⌝ }}}.

Module Type RAFTLOG__LASTINDEX.
  Parameter wp_raftLog__lastIndex_at : wp_raftLog__lastIndex_at_body.
  Arguments wp_raftLog__lastIndex_at {_ _ _ _ _ _ _ _}.
End RAFTLOG__LASTINDEX.
