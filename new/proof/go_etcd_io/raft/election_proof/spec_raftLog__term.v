Require Export New.proof.go_etcd_io.raft.election_proof.inv_raft_phys.
Require Export New.proof.go_etcd_io.raft.election_proof.plog.

(** [l.term(i)]: the term of index [i].

    **Total** (changed 2026-09-21).  It used to take
    [prev.index ≤ i ≤ prev.index + |sents| + |uents|] as a premise and
    conclude [err = interface.nil].  [maybeSendAppend] cannot supply that
    premise -- it calls [r.raftLog.term(pr.Next - 1)] and nothing in
    [own_progress] bounds a peer's [Next] against the log -- and the Go code
    does not assume it either: it branches on [err != nil] into
    [maybeSendSnapshot].  So the premise moved into the conclusion.

    That the triple can be total is a fact about the body
    ([raftLog__termⁱᵐᵖˡ], new/code/go_etcd_io/raft/v3.v:1063): it returns
    [(0, ErrCompacted)] for [i+1 < firstIndex] and [(0, ErrUnavailable)] for
    [i > lastIndex], and inside the range it asks [unstable.maybeTerm] and
    then [Storage.Term], whose error path -- the only [panic] in the
    function -- is excluded by [is_Storage]'s [HTerm].  Both [firstIndex]
    and [lastIndex] are called on the log itself, which is why both are
    postulates of this collection along with [unstable.maybeTerm].

    The conclusion is an **iff**: the error is [nil] exactly on the range the
    old premise described.  Both halves are used.  [lastEntryID] calls [term]
    at [lastIndex] and needs [←] to kill its [Panicf].  [maybeSendAppend]
    needs [→]: having tested [err != nil] and fallen through, it calls
    [r.raftLog.entries(pr.Next, …)], whose premise is
    [prev.index + 1 ≤ pr.Next] -- and the only thing that establishes it is
    that [term(pr.Next - 1)] succeeded.  (The [-1] does not spoil it: at
    [pr.Next = 0] the argument is [2^64 - 1], which [Hnowrap] puts outside
    the range, so [pr.Next ≠ 0] and the subtraction does not wrap.)

    **Which error** (since 2026-10-01): a non-[nil] error is the value
    of one of the two globals [ErrCompacted], [ErrUnavailable] -- the last
    conjunct, stated by the globals' (persistent) points-tos since their
    values are only known through [is_initialized].  [handleAppendEntries]
    needs it: its reject path passes [term(m.Index)] straight to
    [zeroTermOnOutOfBounds], which [Panicf]s on any other error, and
    [m.Index] may well be past the last index there.  Which of the two
    goes with which side of the range is true but not stated; nothing
    needs it.

    **The returned term is pinned** (since 2026-10-01): on the [nil]
    branch it is [plog_term_at prev (sents ++ uents) i] ([plog.v]), the
    term of the log the protocol model sees.  Log replication needs it --
    [matchTerm], and through it [findConflict], [maybeAppend] and
    [maybeCommit], compare it.  In the unstable window it comes from
    [unstable.maybeTerm]'s widened spec, below it from [is_Storage]'s
    [HTerm] ([term_at prev stored i]), which agrees with [plog_term_at] on
    the visible stable prefix [sents] ([proof_raftLog__term.v]).  Until
    then the term was unspecified and nothing on the election path read
    it. *)
Definition wp_raftLog__term_body :=
  ∀ (ext : ffi_syntax) (ffi : ffi_model) (ffi_interp0 : ffi_interp ffi)
    (Σ : gFunctors) (hG : heapGS Σ) (ffi_semantics0 : ffi_semantics ext ffi)
    (sem : go.Semantics) (package_sem : raft.Assumptions)
    (l : loc) (ls : logstate.t) (i : w64),
  {{{ is_pkg_init raft ∗ "Hlog" ∷ own_raftLog l ls }}}
    l @! (go.PointerType raft.raftLog) @! "term" #i
  {{{ (t : w64) (err : interface.t), RET (#t, #err);
      own_raftLog l ls ∗
      ⌜ err = interface.nil ↔
        (uint.Z ls.(logstate.prev).(raft.entryID.index') ≤ uint.Z i ≤
         uint.Z ls.(logstate.prev).(raft.entryID.index') + Z.of_nat (length ls.(logstate.sents))
         + Z.of_nat (length ls.(logstate.uents)))%Z ⌝ ∗
      ⌜ err = interface.nil →
        plog_term_at ls.(logstate.prev) (ls.(logstate.sents) ++ ls.(logstate.uents)) i = Some t ⌝ ∗
      (⌜ err = interface.nil ⌝ ∨ (global_addr raft.ErrCompacted) ↦□ err ∨
       (global_addr raft.ErrUnavailable) ↦□ err) }}}.

Module Type RAFTLOG__TERM.
  Parameter wp_raftLog__term : wp_raftLog__term_body.
  Arguments wp_raftLog__term {_ _ _ _ _ _ _ _}.
End RAFTLOG__TERM.
