Require Export New.proof.go_etcd_io.raft.election_proof.inv_raft_phys.

(** [l.entries(i, maxSize)] -- the log from index [i] on, capped
    ([raftLog__entriesⁱᵐᵖˡ], new/code/go_etcd_io/raft/v3.v:1102):

      if i > l.lastIndex() { return nil, nil }
      return l.slice(i, l.lastIndex()+1, maxSize)

    So the error is always [nil] on this path, and the only premise is the
    lower one: [i] must not be below the compaction boundary, or
    [raftLog.slice] would return [ErrCompacted] (and the caller,
    [maybeSendAppend], would go to [maybeSendSnapshot]).  The empty return
    is *not* an error -- a peer whose [Next] is past the end of the log gets
    an empty [MsgApp].

    The result is read-only and the caller's for good, like
    [raftLog.slice]'s, and the log comes back unchanged.  Its contents are
    not described, because [maybeSendAppend] only takes its length (for
    [Progress.SentEntries]) and its payload size, and puts it in a
    message.  (Until 2026-09-29 it was lent, and the log came back "on loan
    of the page", [logstate.page].) *)
Definition wp_raftLog__entries_body :=
  ∀ (ext : ffi_syntax) (ffi : ffi_model) (ffi_interp0 : ffi_interp ffi)
    (Σ : gFunctors) (hG : heapGS Σ) (ffi_semantics0 : ffi_semantics ext ffi)
    (sem : go.Semantics) (package_sem : raft.Assumptions)
    (l : loc) (ls : logstate.t) (i maxSize : w64),
  (uint.Z ls.(logstate.prev).(raft.entryID.index') + 1 ≤ uint.Z i)%Z →
  {{{ is_pkg_init raft ∗ "Hlog" ∷ own_raftLog l ls }}}
    l @! (go.PointerType raft.raftLog) @! "entries" #i #maxSize
  {{{ (s : slice.t) (es : list raftpb.Entry.t),
      RET (#s, #interface.nil);
      own_raftLog l ls ∗ s ↦*□ es ∗
      (* every entry returned is an entry of the log, and they are the
         log's from [i] on, cut short by [maxSize] ([raftLog.slice]) *)
      ⌜ (∀ e, e ∈ es → e ∈ ls.(logstate.sents) ++ ls.(logstate.uents)) ∧
        es `prefix_of` plog_from ls.(logstate.prev)
                         (ls.(logstate.sents) ++ ls.(logstate.uents)) i ⌝ }}}.

Module Type RAFTLOG__ENTRIES.
  Parameter wp_raftLog__entries : wp_raftLog__entries_body.
  Arguments wp_raftLog__entries {_ _ _ _ _ _ _ _}.
End RAFTLOG__ENTRIES.
