Require Export New.proof.go_etcd_io.raft.election_proof.inv_raft_phys.

(** [payloadSize(e)]: the size of one entry's payload, i.e. [len(e.Data)]
    ([payloadSizeⁱᵐᵖˡ], new/code/go_etcd_io/raft/v3.v:7515).

    The entry is passed **by value** -- Goose allocates a local for it -- so
    the triple needs no ownership at all: the length of a slice *value* is a
    projection of that value, not something read out of the heap.  The result
    is therefore pinned exactly, [e.Data.len], which is what
    [payloadsSize]'s caller needs in order to see that a batch of empty
    entries has zero payload. *)
Definition wp_payloadSize_body :=
  ∀ (ext : ffi_syntax) (ffi : ffi_model) (ffi_interp0 : ffi_interp ffi)
    (Σ : gFunctors) (hG : heapGS Σ) (ffi_semantics0 : ffi_semantics ext ffi)
    (sem : go.Semantics) (package_sem : raft.Assumptions)
    (e : raftpb.Entry.t),
  {{{ is_pkg_init raft }}}
    @! raft.payloadSize #e
  {{{ RET #(e.(raftpb.Entry.Data').(slice.len)); True }}}.

Module Type PAYLOADSIZE.
  Parameter wp_payloadSize : wp_payloadSize_body.
  Arguments wp_payloadSize {_ _ _ _ _ _ _ _}.
End PAYLOADSIZE.
