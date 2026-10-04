Require Export New.proof.go_etcd_io.raft.election_proof.inv_raft_phys.

(** [ro.heartbeatCtx()] ([readOnly__heartbeatCtxⁱᵐᵖˡ],
    new/code/go_etcd_io/raft/v3.v:6329; [read_only.go:93]):

      if len(ro.unconfirmedReads) == 0 { return nil }
      pos := ro.confirmedReads + uint64(len(ro.unconfirmedReads))
      enc := make([]byte, 8)
      binary.LittleEndian.PutUint64(enc, pos)
      return enc

    No panic.  With no pending request the result is [nil] -- under the
    phase-1 scope ([own_raft_misc]'s [pending = []]) always, which is what
    [bcastHeartbeat] relies on.  Otherwise a fresh eight-byte slice, fully
    owned, holding [readonly_position r] little-endian ([u64_le]).  The
    object is unchanged.  The receiver is a pointer and the body reads
    [ro.unconfirmedReads] through it, so the spec owns the object. *)
Definition wp_readOnly__heartbeatCtx_body :=
  ∀ (ext : ffi_syntax) (ffi : ffi_model) (ffi_interp0 : ffi_interp ffi)
    (Σ : gFunctors) (hG : heapGS Σ) (ffi_semantics0 : ffi_semantics ext ffi)
    (sem : go.Semantics) (package_sem : raft.Assumptions)
    (ro : loc) (r : readonly.t),
  {{{ is_pkg_init raft ∗ "Hown" ∷ own_ReadOnly ro r }}}
    ro @! (go.PointerType raft.readOnly) @! "heartbeatCtx" #()
  {{{ (sl : slice.t), RET #sl;
      own_ReadOnly ro r ∗
      (⌜ r.(readonly.pending) = [] ∧ sl = slice.nil ⌝ ∨
       ⌜ r.(readonly.pending) ≠ [] ⌝ ∗
       sl ↦* u64_le (readonly_position r) ∗
       own_slice_cap w8 sl (DfracOwn 1)) }}}.

Module Type READONLY__HEARTBEATCTX.
  Parameter wp_readOnly__heartbeatCtx : wp_readOnly__heartbeatCtx_body.
  Arguments wp_readOnly__heartbeatCtx {_ _ _ _ _ _ _ _}.
End READONLY__HEARTBEATCTX.
