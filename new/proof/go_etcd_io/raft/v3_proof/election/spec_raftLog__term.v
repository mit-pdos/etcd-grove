Require Export New.proof.go_etcd_io.raft.v3_proof.election.inv_raft_phys.

(** [l.term(i)]: the term of index [i], for an [i] the log covers.

    Stated at a fixed split ([_at]).  The range premise is what makes the
    [Panicf] unreachable: [term] errors outside
    [[firstIndex - 1, lastIndex]] and then panics, and the proof discharges
    that by calling [firstIndex] and [lastIndex] on the log itself -- which
    is why both are postulates here, along with [unstable.maybeTerm] for the
    part of the range the unstable suffix covers.

    The returned term is not specified.  Nothing on the election path reads
    it: [lastEntryID] only puts it in an [entryID], and [isUpToDate]
    comparing the wrong terms can only make the node decline to vote, which
    is always protocol-legal. *)
Definition wp_raftLog__term_at_body :=
  ∀ (ext : ffi_syntax) (ffi : ffi_model) (ffi_interp0 : ffi_interp ffi)
    (Σ : gFunctors) (hG : heapGS Σ) (ffi_semantics0 : ffi_semantics ext ffi)
    (sem : go.Semantics) (package_sem : raft.Assumptions)
    (l : loc) prev sents uents (i : w64),
  (uint.Z prev.(raft.entryID.index') ≤ uint.Z i ≤
   uint.Z prev.(raft.entryID.index') + Z.of_nat (length sents)
   + Z.of_nat (length uents))%Z →
  {{{ is_pkg_init raft ∗ "Hlog" ∷ own_raftLog_at l prev sents uents }}}
    l @! (go.PointerType raft.raftLog) @! "term" #i
  {{{ (t : w64), RET (#t, #interface.nil);
      own_raftLog_at l prev sents uents }}}.

Module Type RAFTLOG__TERM.
  Parameter wp_raftLog__term_at : wp_raftLog__term_at_body.
  Arguments wp_raftLog__term_at {_ _ _ _ _ _ _ _}.
End RAFTLOG__TERM.
