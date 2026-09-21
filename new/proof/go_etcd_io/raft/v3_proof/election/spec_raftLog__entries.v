Require Export New.proof.go_etcd_io.raft.v3_proof.election.inv_raft_phys.

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

    The page is **lent**, like [raftLog.slice]'s: in two of the three cases
    it aliases the log.  Its contents are not described, because
    [maybeSendAppend] only takes its length (for [Progress.SentEntries]) and
    its payload size, and puts it in a message.

    [l ↦ lv] comes back with the page and the wand takes both, for the
    reason spelled out in [spec_raftLog__slice.v]: the page aliases an
    *entry buffer*, never the [raftLog] record, and [maybeSendAppend] has
    to read [r.raftLog.committed] and run [send] while still holding the
    page.  ([send] is stated on [own_raft_bare], which does not ask for
    the log at all -- see [spec_raft__send.v].) *)
Definition wp_raftLog__entries_at_body :=
  ∀ (ext : ffi_syntax) (ffi : ffi_model) (ffi_interp0 : ffi_interp ffi)
    (Σ : gFunctors) (hG : heapGS Σ) (ffi_semantics0 : ffi_semantics ext ffi)
    (sem : go.Semantics) (package_sem : raft.Assumptions)
    (l : loc) prev sents uents (i maxSize : w64),
  (uint.Z prev.(raft.entryID.index') + 1 ≤ uint.Z i)%Z →
  {{{ is_pkg_init raft ∗ "Hlog" ∷ own_raftLog_at l prev sents uents }}}
    l @! (go.PointerType raft.raftLog) @! "entries" #i #maxSize
  {{{ (s : slice.t) (es : list raftpb.Entry.t) (dq : dfrac)
      (lv : raft.raftLog.t),
      RET (#s, #interface.nil);
      l ↦ lv ∗ s ↦*{dq} es ∗
      (l ↦ lv -∗ s ↦*{dq} es -∗ own_raftLog_at l prev sents uents) }}}.

Module Type RAFTLOG__ENTRIES.
  Parameter wp_raftLog__entries_at : wp_raftLog__entries_at_body.
  Arguments wp_raftLog__entries_at {_ _ _ _ _ _ _ _}.
End RAFTLOG__ENTRIES.
