Require Export New.proof.go_etcd_io.raft.election_proof.inv_raft_phys.

(** [u.maybeTerm(i)]: the term of index [i] if the unstable suffix covers
    it, or if [i] is a pending snapshot's index.  [ok] pins down exactly
    which indices those are, which is what [raftLog.term] needs in order to
    decide whether to fall through to [Storage].
    As with the other two [maybe*] methods, on a bare [*unstable], with the
    snapshot pointer as [own_snap].  The [i >= offset] branch calls
    [maybeLastIndex], which is why that is a postulate here.
    When [ok], [t] is the term of the entry at [i] (since 2026-10-01, for
    [raftLog.term]'s widened spec; before, only [ok] was pinned), or the
    snapshot's term at the snapshot's index (since 2026-10-02).
    The first premise -- a pending snapshot ends right below [offset] -- is
    what [unstable.restore] establishes and [own_raftLog] keeps ([Hoffset]
    with [sents = []]).  Without it the [i >= offset] branch, after
    [maybeLastIndex] returned the snapshot's index, could index
    [u.entries] out of bounds. *)
Definition wp_unstable__maybeTerm_body :=
  ∀ (ext : ffi_syntax) (ffi : ffi_model) (ffi_interp0 : ffi_interp ffi)
    (Σ : gFunctors) (hG : heapGS Σ) (ffi_semantics0 : ffi_semantics ext ffi)
    (sem : go.Semantics) (package_sem : raft.Assumptions)
    (u : loc) (uv : raft.unstable.t)
      (uents : list raftpb.Entry.t) (snap : option raft.entryID.t) (i : w64),
  (∀ sid, snap = Some sid →
     uint.Z uv.(raft.unstable.offset') = uint.Z sid.(raft.entryID.index') + 1)%Z →
  (uint.Z uv.(raft.unstable.offset') + Z.of_nat (length uents) < 2^64)%Z →
  {{{ is_pkg_init raft ∗ "Hun" ∷ own_unstable u uv uents ∗
      "#Hsnap" ∷ own_snap uv.(raft.unstable.snapshot') snap }}}
    u @! (go.PointerType raft.unstable) @! "maybeTerm" #i
  {{{ (t : w64) (ok : bool), RET (#t, #ok);
      own_unstable u uv uents ∗
      ⌜ ok = true ↔ ((uint.Z uv.(raft.unstable.offset') ≤ uint.Z i <
                      uint.Z uv.(raft.unstable.offset') + Z.of_nat (length uents))%Z ∨
                     ∃ sid, snap = Some sid ∧ i = sid.(raft.entryID.index')) ⌝ ∗
      ⌜ ok = true →
        ((uint.Z uv.(raft.unstable.offset') ≤ uint.Z i <
          uint.Z uv.(raft.unstable.offset') + Z.of_nat (length uents))%Z ∧
         ∃ e, uents !! Z.to_nat (uint.Z i - uint.Z uv.(raft.unstable.offset')) = Some e ∧
              t = e.(raftpb.Entry.Term')) ∨
        (∃ sid, snap = Some sid ∧ i = sid.(raft.entryID.index') ∧
                t = sid.(raft.entryID.term')) ⌝ }}}.

Module Type UNSTABLE__MAYBETERM.
  Parameter wp_unstable__maybeTerm : wp_unstable__maybeTerm_body.
  Arguments wp_unstable__maybeTerm {_ _ _ _ _ _ _ _}.
End UNSTABLE__MAYBETERM.
