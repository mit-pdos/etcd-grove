Require Export New.proof.go_etcd_io.raft.election_proof.inv_raft_phys.

(** [MajorityConfig.Slice] returns the ids of the set, sorted.  Stated on
    [own_idset_opt] ([inv_tracker.v]) so that it covers the [nil] sets a
    simple configuration carries ([Voters[1]], [Learners], [LearnersNext]),
    for which the result is the empty (nil) slice.  Sortedness is not
    stated -- [slices.Sort]'s triple gives only a permutation, and nothing
    downstream needs more. *)
Definition wp_MajorityConfig__Slice_body :=
  ∀ (ext : ffi_syntax) (ffi : ffi_model) (ffi_interp0 : ffi_interp ffi)
    (Σ : gFunctors) (hG : heapGS Σ) (ffi_semantics0 : ffi_semantics ext ffi)
    (sem : go.Semantics) (package_sem : raft.Assumptions)
    (m : loc) (ids : gmap w64 unit),
  {{{ is_pkg_init quorum ∗ own_idset_opt m ids }}}
    m @! quorum.MajorityConfig @! "Slice" #()
  {{{ (sl : slice.t) (xs : list w64), RET #sl;
      own_idset_opt m ids ∗ sl ↦* xs ∗ own_slice_cap w64 sl (DfracOwn 1) ∗
      ⌜ xs ≡ₚ elements (dom ids) ⌝ }}}.

Module Type MAJORITYCONFIG__SLICE.
  Parameter wp_MajorityConfig__Slice : wp_MajorityConfig__Slice_body.
  Arguments wp_MajorityConfig__Slice {_ _ _ _ _ _ _ _}.
End MAJORITYCONFIG__SLICE.
