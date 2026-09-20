Require Export New.proof.go_etcd_io.raft.v3_proof.election.inv_raft_phys.

(** [extend(dst, vals)]: [dst ++ vals] in a slice allocated to exactly the
    needed length ([util.go], "allocates only once").

    **Restricted to the allocating branch**: the premise says the
    concatenation does not fit in [cap(dst)], so the [append(dst, vals...)]
    in-place branch is dead.  That branch would write into [dst]'s spare
    capacity, which this triple does not own -- and must not: the only
    caller, [raftLog.slice], passes a slice the [Storage] lent it, and
    [Storage.Entries]'s contract ([inv_storage.v]) guarantees [cap = len]
    precisely so that the branch is never taken.  A triple for the in-place
    branch would need [own_slice_cap dst]; widen this one when a caller has
    it, rather than adding a second.

    Both inputs are only read and come back at their fractions; the result
    is fresh and fully owned. *)
Definition wp_extend_body :=
  ∀ (ext : ffi_syntax) (ffi : ffi_model) (ffi_interp0 : ffi_interp ffi)
    (Σ : gFunctors) (hG : heapGS Σ) (ffi_semantics0 : ffi_semantics ext ffi)
    (sem : go.Semantics) (package_sem : raft.Assumptions)
    (dst vals : slice.t) (ds vs : list raftpb.Entry.t) (dq1 dq2 : dfrac),
  (sint.Z dst.(slice.cap) < Z.of_nat (length ds) + Z.of_nat (length vs))%Z →
  (Z.of_nat (length ds) + Z.of_nat (length vs) < 2^63)%Z →
  {{{ is_pkg_init raft ∗ "Hdst" ∷ dst ↦*{dq1} ds ∗ "Hvals" ∷ vals ↦*{dq2} vs }}}
    @! raft.extend #dst #vals
  {{{ (s : slice.t), RET #s;
      s ↦* (ds ++ vs) ∗ own_slice_cap raftpb.Entry.t s (DfracOwn 1) ∗
      dst ↦*{dq1} ds ∗ vals ↦*{dq2} vs }}}.

Module Type EXTEND.
  Parameter wp_extend : wp_extend_body.
  Arguments wp_extend {_ _ _ _ _ _ _ _}.
End EXTEND.
