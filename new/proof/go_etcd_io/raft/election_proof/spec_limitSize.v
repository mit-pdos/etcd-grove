Require Export New.proof.go_etcd_io.raft.election_proof.inv_raft_phys.

(** [limitSize(ents, maxSize)]: the longest prefix of [ents] whose encoded
    size fits in [maxSize], except that a non-empty input always yields at
    least its first entry ([util.go:268]).

    The result is [ents] itself or [ents[:limit]], so it **aliases** the
    input and is lent: the postcondition gives the prefix's points-to and a
    wand back to the whole slice.  Which prefix is not specified beyond its
    length bounds, because the sizes come from [Entry.Size] (pointer receiver)
    ([spec_Entry__Size.v]), about whose value nothing is known -- and
    nothing on the election path cares where the slice is cut. *)
Definition wp_limitSize_body :=
  ∀ (ext : ffi_syntax) (ffi : ffi_model) (ffi_interp0 : ffi_interp ffi)
    (Σ : gFunctors) (hG : heapGS Σ) (ffi_semantics0 : ffi_semantics ext ffi)
    (sem : go.Semantics) (package_sem : raft.Assumptions)
    (s : slice.t) (es : list raftpb.Entry.t) (dq : dfrac) (maxSize : w64),
  {{{ is_pkg_init raft ∗ "Hs" ∷ s ↦*{dq} es }}}
    @! raft.limitSize #s #maxSize
  {{{ (s' : slice.t) (n : nat), RET #s';
      ⌜ (n ≤ length es)%nat ∧ (es ≠ [] → (1 ≤ n)%nat) ⌝ ∗
      s' ↦*{dq} take n es ∗
      (s' ↦*{dq} take n es -∗ s ↦*{dq} es) }}}.

Module Type LIMITSIZE.
  Parameter wp_limitSize : wp_limitSize_body.
  Arguments wp_limitSize {_ _ _ _ _ _ _ _}.
End LIMITSIZE.
