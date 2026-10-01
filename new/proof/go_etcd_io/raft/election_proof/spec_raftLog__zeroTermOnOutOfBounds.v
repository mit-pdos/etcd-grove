Require Export New.proof.go_etcd_io.raft.election_proof.inv_raft_phys.
Require Export New.proof.go_etcd_io.raft.election_proof.plog.

(** [l.zeroTermOnOutOfBounds(t, err)], at a [nil] error: returns [t].

    The body ([raftLog__zeroTermOnOutOfBoundsⁱᵐᵖˡ],
    new/code/go_etcd_io/raft/v3.v:1393) returns [t] for [err == nil], [0]
    for [err == ErrCompacted || err == ErrUnavailable], and [Panicf]s
    otherwise.  **Only the [nil] case is specified**, as a premise.  The
    other two would need, besides naming the two globals' values, that
    they are comparable -- [err == ErrCompacted] with a non-[nil] [err]
    is stuck on [CheckComparable] unless the dynamic type is known to be a
    pointer ([is_new_error], [v3_proof/base.v]), and [is_initialized]
    asserts that only of [ErrSnapshotTemporarilyUnavailable].  The one
    caller, [findConflict], only calls it at an index in
    [[prev.index, last]] (its own premise puts every batch entry at or
    above [prev.index], and it tests [id.index <= lastIndex()]), where
    [term] returns a [nil] error.  The result only feeds an [Infof].

    The receiver is read only on the [Panicf] path, so the spec needs no
    ownership of the log. *)
Definition wp_raftLog__zeroTermOnOutOfBounds_body :=
  ∀ (ext : ffi_syntax) (ffi : ffi_model) (ffi_interp0 : ffi_interp ffi)
    (Σ : gFunctors) (hG : heapGS Σ) (ffi_semantics0 : ffi_semantics ext ffi)
    (sem : go.Semantics) (package_sem : raft.Assumptions)
    (l : loc) (t : w64) (err : interface.t),
  err = interface.nil →
  {{{ is_pkg_init raft }}}
    l @! (go.PointerType raft.raftLog) @! "zeroTermOnOutOfBounds" #t #err
  {{{ RET #t; True }}}.

Module Type RAFTLOG__ZEROTERMONOUTOFBOUNDS.
  Parameter wp_raftLog__zeroTermOnOutOfBounds : wp_raftLog__zeroTermOnOutOfBounds_body.
  Arguments wp_raftLog__zeroTermOnOutOfBounds {_ _ _ _ _ _ _ _}.
End RAFTLOG__ZEROTERMONOUTOFBOUNDS.
