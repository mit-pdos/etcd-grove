Require Export New.proof.go_etcd_io.raft.election_proof.inv_raft_phys.

(** [u.maybeTerm(i)]: the term of index [i] if the unstable suffix covers
    it.  [ok] pins down exactly which indices those are, which is what
    [raftLog.term] needs in order to decide whether to fall through to
    [Storage].

    As with the other two [maybe*] methods, on a bare [*unstable] and with
    [snapshot = nil] as a premise.  The [i >= offset] branch calls
    [maybeLastIndex], which is why that is a postulate here.

    When [ok], [t] is the term of the entry at [i] (since 2026-10-01, for
    [raftLog.term]'s widened spec; before, only [ok] was pinned). *)
Definition wp_unstable__maybeTerm_body :=
  ∀ (ext : ffi_syntax) (ffi : ffi_model) (ffi_interp0 : ffi_interp ffi)
    (Σ : gFunctors) (hG : heapGS Σ) (ffi_semantics0 : ffi_semantics ext ffi)
    (sem : go.Semantics) (package_sem : raft.Assumptions)
    (u : loc) (uv : raft.unstable.t)
      (uents : list raftpb.Entry.t) (i : w64),
  uv.(raft.unstable.snapshot') = null →
  (uint.Z uv.(raft.unstable.offset') + Z.of_nat (length uents) < 2^64)%Z →
  {{{ is_pkg_init raft ∗ "Hun" ∷ own_unstable u uv uents }}}
    u @! (go.PointerType raft.unstable) @! "maybeTerm" #i
  {{{ (t : w64) (ok : bool), RET (#t, #ok);
      own_unstable u uv uents ∗
      ⌜ ok = true ↔ (uint.Z uv.(raft.unstable.offset') ≤ uint.Z i <
                     uint.Z uv.(raft.unstable.offset') + Z.of_nat (length uents))%Z ⌝ ∗
      ⌜ ok = true → ∃ e, uents !! Z.to_nat (uint.Z i - uint.Z uv.(raft.unstable.offset')) = Some e ∧
                         t = e.(raftpb.Entry.Term') ⌝ }}}.

Module Type UNSTABLE__MAYBETERM.
  Parameter wp_unstable__maybeTerm : wp_unstable__maybeTerm_body.
  Arguments wp_unstable__maybeTerm {_ _ _ _ _ _ _ _}.
End UNSTABLE__MAYBETERM.
