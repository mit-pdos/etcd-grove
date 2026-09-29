Require Export New.proof.go_etcd_io.raft.election_proof.inv_raft_phys.

(** [l.slice(lo, hi, maxSize)]: a non-empty prefix of the log entries at
    [[lo, hi)], cut to roughly [maxSize] bytes ([log.go:497]).

    Stated at the log's state [ls]: it calls
    [mustCheckOutOfBounds] (hence [firstIndex]/[lastIndex]) and reads the
    unstable suffix and the [Storage] directly.  The range premise makes every failure path dead:
    [mustCheckOutOfBounds] returns [nil], [Storage.Entries] cannot return
    [ErrCompacted]/[ErrUnavailable] (the contract in [inv_storage.v] says
    so on this range), so the [Panicf] and the [panic] are unreachable, and
    [lo < hi] rules out the empty early return.

    The result **aliases the log** in two of the three cases (a sub-slice
    of [unstable.entries], or one the [Storage] handed out); in the third
    (a range spanning the stable/unstable boundary) it is a fresh slice
    from [extend].  In every case it is returned **read-only and for
    good**, [s ↦*□ es], and the log comes back unchanged: no entry of the
    log is ever written again once it is in it -- [unstable] never writes
    in place ([own_unstable], [inv_raftlog.v]) and [Storage] promises the
    same ([is_Storage]'s [Entries], [inv_storage.v]) -- so there is nothing
    to give back.  [maybeSendAppend] relies on it: it puts the result in a
    [MsgApp], which [r.msgs] keeps, and reads it again ([payloadsSize])
    after [r.send].  (Until 2026-09-29 the result was *lent*, and the log
    came back "on loan of that page", [logstate.page].)

    What the result *is* is stated only as far as [scan] and its callers
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
  (uint.Z ls.(logstate.prev).(raft.entryID.index') + 1 ≤ uint.Z lo ∧ uint.Z lo < uint.Z hi ∧
   uint.Z hi ≤ uint.Z ls.(logstate.prev).(raft.entryID.index') + Z.of_nat (length ls.(logstate.sents))
   + Z.of_nat (length ls.(logstate.uents)) + 1)%Z →
  {{{ is_pkg_init raft ∗ "Hlog" ∷ own_raftLog l ls }}}
    l @! (go.PointerType raft.raftLog) @! "slice" #lo #hi #maxSize
  {{{ (s : slice.t) (es : list raftpb.Entry.t),
      RET (#s, #interface.nil);
      own_raftLog l ls ∗ s ↦*□ es ∗
      ⌜ es ≠ [] ∧
        (Z.of_nat (length es) ≤ uint.Z hi - uint.Z lo)%Z ∧
        (∀ e, e ∈ es → e ∈ ls.(logstate.sents) ++ ls.(logstate.uents)) ⌝ }}}.

Module Type RAFTLOG__SLICE.
  Parameter wp_raftLog__slice : wp_raftLog__slice_body.
  Arguments wp_raftLog__slice {_ _ _ _ _ _ _ _}.
End RAFTLOG__SLICE.
