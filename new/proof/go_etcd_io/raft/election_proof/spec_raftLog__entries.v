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

    The page is **lent**, like [raftLog.slice]'s: in two of the three cases
    it aliases the log.  Its contents are not described, because
    [maybeSendAppend] only takes its length (for [Progress.SentEntries]) and
    its payload size, and puts it in a message.

    The log comes back on loan of the page ([logstate.page]), as
    [raftLog.slice]'s does, and for the reason spelled out there its struct
    stays readable ([own_raftLog_struct]): [maybeSendAppend] has to read
    [r.raftLog.committed] and run [send] while still holding the page.
    ([send] is called with the log lent to the caller, [nstate.lent] --
    see [spec_raft__send.v].) *)
Definition wp_raftLog__entries_body :=
  ∀ (ext : ffi_syntax) (ffi : ffi_model) (ffi_interp0 : ffi_interp ffi)
    (Σ : gFunctors) (hG : heapGS Σ) (ffi_semantics0 : ffi_semantics ext ffi)
    (sem : go.Semantics) (package_sem : raft.Assumptions)
    (l : loc) (ls : logstate.t) (i maxSize : w64),
  ls.(logstate.page) = None →
  (uint.Z ls.(logstate.prev).(raft.entryID.index') + 1 ≤ uint.Z i)%Z →
  {{{ is_pkg_init raft ∗ "Hlog" ∷ own_raftLog l ls }}}
    l @! (go.PointerType raft.raftLog) @! "entries" #i #maxSize
  {{{ (s : slice.t) (es : list raftpb.Entry.t) (dq : dfrac),
      RET (#s, #interface.nil);
      own_raftLog l (ls <| logstate.page := Some (s, es, dq) |>) ∗ s ↦*{dq} es }}}.

Module Type RAFTLOG__ENTRIES.
  Parameter wp_raftLog__entries : wp_raftLog__entries_body.
  Arguments wp_raftLog__entries {_ _ _ _ _ _ _ _}.
End RAFTLOG__ENTRIES.
