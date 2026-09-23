Require Export New.proof.go_etcd_io.raft.election_proof.inv_raft_phys.

(** [u.slice(lo, hi)]: the entries at [[lo, hi)] of the unstable suffix,
    as a three-index sub-slice [u.entries[lo-off : hi-off : hi-off]] of the
    entry slice.

    The result **aliases** [u.entries], so it is lent: the postcondition
    hands out the sub-slice's points-to and a wand that takes it back and
    restores [u.entries ↦* uents].  Its capacity equals its length (that is
    what the third index buys: an [append] to the result reallocates instead
    of writing into the suffix), which [raftLog.slice] relies on through
    [extend].

    The entries are described only as far as the callers need: their
    number, and that each is an entry of the suffix.  [lo < hi] is required
    rather than [lo <= hi] so that the result is non-empty, which the
    ownership transfer needs (see [own_slice_same_ptr_len]) and which
    [raftLog.scan] needs anyway. *)
Definition wp_unstable__slice_body :=
  ∀ (ext : ffi_syntax) (ffi : ffi_model) (ffi_interp0 : ffi_interp ffi)
    (Σ : gFunctors) (hG : heapGS Σ) (ffi_semantics0 : ffi_semantics ext ffi)
    (sem : go.Semantics) (package_sem : raft.Assumptions)
    (u : loc) (uv : raft.unstable.t) (uents : list raftpb.Entry.t) (lo hi : w64),
  (uint.Z uv.(raft.unstable.offset') ≤ uint.Z lo ∧ uint.Z lo < uint.Z hi ∧
   uint.Z hi ≤ uint.Z uv.(raft.unstable.offset') + Z.of_nat (length uents))%Z →
  (uint.Z uv.(raft.unstable.offset') + Z.of_nat (length uents) < 2^64)%Z →
  {{{ is_pkg_init raft ∗ "Hu" ∷ u ↦ uv ∗
      "Hents" ∷ uv.(raft.unstable.entries') ↦* uents }}}
    u @! (go.PointerType raft.unstable) @! "slice" #lo #hi
  {{{ (s : slice.t) (es : list raftpb.Entry.t), RET #s;
      u ↦ uv ∗ s ↦* es ∗
      ⌜ (Z.of_nat (length es) = uint.Z hi - uint.Z lo)%Z ∧
        (∀ e, e ∈ es → e ∈ uents) ∧
        s.(slice.cap) = s.(slice.len) ⌝ ∗
      (s ↦* es -∗ uv.(raft.unstable.entries') ↦* uents) }}}.

Module Type UNSTABLE__SLICE.
  Parameter wp_unstable__slice : wp_unstable__slice_body.
  Arguments wp_unstable__slice {_ _ _ _ _ _ _ _}.
End UNSTABLE__SLICE.
