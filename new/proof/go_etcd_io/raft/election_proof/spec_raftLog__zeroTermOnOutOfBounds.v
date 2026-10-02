Require Export New.proof.go_etcd_io.raft.election_proof.inv_raft_phys.
Require Export New.proof.go_etcd_io.raft.election_proof.plog.

(** [l.zeroTermOnOutOfBounds(t, err)]: [t] for a [nil] error, [0] for
    [ErrCompacted] / [ErrUnavailable].

    The body ([raftLog__zeroTermOnOutOfBoundsⁱᵐᵖˡ],
    new/code/go_etcd_io/raft/v3.v:1393) returns [t] for [err == nil], [0]
    for [err == ErrCompacted || err == ErrUnavailable], and [Panicf]s
    otherwise.  The premise -- [err] is [nil] or the value of one of the
    two globals -- is exactly what [raftLog.term]'s last conjunct gives,
    and every caller passes [term]'s result straight in.

    Until 2026-10-01 only the [nil] case was specified (as a pure
    premise): comparing a non-[nil] [err] against [ErrCompacted] is stuck
    on [CheckComparable] unless the dynamic type is known to be a pointer,
    and [is_initialized] did not say so.  It now does ([is_new_error] for
    both globals, [v3_proof/base.v]).  Widened for [handleAppendEntries],
    whose reject path calls [zeroTermOnOutOfBounds(term(m.Index))] with
    [m.Index] possibly past the last index, i.e. with [ErrUnavailable].
    The result only feeds a [Debugf] there (and an [Infof] in
    [findConflict]), so all that is said about it is that it is [t] on the
    [nil] branch.

    The receiver is read only on the [Panicf] path, so the spec needs no
    ownership of the log. *)
Definition wp_raftLog__zeroTermOnOutOfBounds_body :=
  ∀ (ext : ffi_syntax) (ffi : ffi_model) (ffi_interp0 : ffi_interp ffi)
    (Σ : gFunctors) (hG : heapGS Σ) (ffi_semantics0 : ffi_semantics ext ffi)
    (sem : go.Semantics) (package_sem : raft.Assumptions)
    (l : loc) (t : w64) (err : interface.t),
  {{{ is_pkg_init raft ∗
      "#Herr" ∷ (⌜ err = interface.nil ⌝ ∨ (global_addr raft.ErrCompacted) ↦□ err ∨
                 (global_addr raft.ErrUnavailable) ↦□ err) }}}
    l @! (go.PointerType raft.raftLog) @! "zeroTermOnOutOfBounds" #t #err
  {{{ (t' : w64), RET #t'; ⌜ err = interface.nil → t' = t ⌝ }}}.

Module Type RAFTLOG__ZEROTERMONOUTOFBOUNDS.
  Parameter wp_raftLog__zeroTermOnOutOfBounds : wp_raftLog__zeroTermOnOutOfBounds_body.
  Arguments wp_raftLog__zeroTermOnOutOfBounds {_ _ _ _ _ _ _ _}.
End RAFTLOG__ZEROTERMONOUTOFBOUNDS.
