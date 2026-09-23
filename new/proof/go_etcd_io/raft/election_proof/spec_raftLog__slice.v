Require Export New.proof.go_etcd_io.raft.election_proof.inv_raft_phys.

(** [l.slice(lo, hi, maxSize)]: a non-empty prefix of the log entries at
    [[lo, hi)], cut to roughly [maxSize] bytes ([log.go:497]).

    Stated at the log's state [ls], at no page: it calls
    [mustCheckOutOfBounds] (hence [firstIndex]/[lastIndex]) and reads the
    unstable suffix and the [Storage] directly.  The range premise makes every failure path dead:
    [mustCheckOutOfBounds] returns [nil], [Storage.Entries] cannot return
    [ErrCompacted]/[ErrUnavailable] (the contract in [inv_storage.v] says
    so on this range), so the [Panicf] and the [panic] are unreachable, and
    [lo < hi] rules out the empty early return.

    The result **aliases the log** in two of the three cases (a sub-slice
    of [unstable.entries], or one the [Storage] lent), so it is lent: the
    postcondition gives the page's points-to at some fraction, and the log
    comes back at [ls <| page := Some (s, es, dq) |>] -- on loan of that
    page ([logstate.page], [inv_raftlog.v]); [own_raftLog_return_page] ends
    the loan.  In the third case (a page spanning the stable/unstable
    boundary) the page is a fresh slice from [extend] and returning it
    simply drops it.

    **The [raftLog] struct itself stays readable while the page is out**
    (2026-09-21; since 2026-09-23 through [own_raftLog_struct]).  What the
    page aliases is an *entry buffer* -- [unstable.entries], or one the
    [Storage] lent -- never the [raftLog] record at [l], which is a
    separate allocation that [slice] only reads through.  So the paged
    [own_raftLog] keeps [l ↦ lv] outside the loan's wand.  [maybeSendAppend]
    is what needs it: it holds the page from [raftLog.entries] across
    [r.send(...)] (nothing else can give it the page back afterwards, and
    [payloadsSize] needs it), and in between the message literal reads
    [r.raftLog.committed].  With the old form the log was entirely
    unavailable for the whole of that window, so the field read could not
    be stepped at all.

    What the page *is* is stated only as far as [scan] and its callers
    need: non-empty, at most [hi - lo] entries, every one an entry of the
    log.  That is enough for [hasUnappliedConfChanges] ([HnoConfChange] is
    a fact about every entry) and for [scan]'s progress.  If a later caller
    needs the indices -- [maybeSendAppend] will -- strengthen this triple
    rather than adding a second one. *)
Definition wp_raftLog__slice_body :=
  ∀ (ext : ffi_syntax) (ffi : ffi_model) (ffi_interp0 : ffi_interp ffi)
    (Σ : gFunctors) (hG : heapGS Σ) (ffi_semantics0 : ffi_semantics ext ffi)
    (sem : go.Semantics) (package_sem : raft.Assumptions)
    (l : loc) (ls : logstate.t) (lo hi maxSize : w64),
  ls.(logstate.page) = None →
  (uint.Z ls.(logstate.prev).(raft.entryID.index') + 1 ≤ uint.Z lo ∧ uint.Z lo < uint.Z hi ∧
   uint.Z hi ≤ uint.Z ls.(logstate.prev).(raft.entryID.index') + Z.of_nat (length ls.(logstate.sents))
   + Z.of_nat (length ls.(logstate.uents)) + 1)%Z →
  {{{ is_pkg_init raft ∗ "Hlog" ∷ own_raftLog l ls }}}
    l @! (go.PointerType raft.raftLog) @! "slice" #lo #hi #maxSize
  {{{ (s : slice.t) (es : list raftpb.Entry.t) (dq : dfrac),
      RET (#s, #interface.nil);
      own_raftLog l (ls <| logstate.page := Some (s, es, dq) |>) ∗ s ↦*{dq} es ∗
      ⌜ es ≠ [] ∧
        (Z.of_nat (length es) ≤ uint.Z hi - uint.Z lo)%Z ∧
        (∀ e, e ∈ es → e ∈ ls.(logstate.sents) ++ ls.(logstate.uents)) ⌝ }}}.

Module Type RAFTLOG__SLICE.
  Parameter wp_raftLog__slice : wp_raftLog__slice_body.
  Arguments wp_raftLog__slice {_ _ _ _ _ _ _ _}.
End RAFTLOG__SLICE.
