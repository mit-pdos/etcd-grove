Require Export New.proof.go_etcd_io.raft.election_proof.inv_raft_phys.

(** [ro.recvAck(from, ctx)] ([readOnly__recvAckⁱᵐᵖˡ],
    new/code/go_etcd_io/raft/v3.v:6267; [read_only.go:65]):

      if len(ctx) != 0 {
          ro.acks[from] = max(ro.acks[from], binary.LittleEndian.Uint64(ctx))
      }

    The context is a heartbeat's: the first eight bytes, little-endian, are
    a *position* ([readonly_position] of the leader when it sent the
    heartbeat), and the voter's ack becomes the larger of that and its old
    one ([readonly_recvAck]).  A non-empty context shorter than eight bytes
    makes [Uint64] panic (index out of range); a peer's [Context] can be
    anything, and nothing in the state excludes it, so the spec takes
    [cs = [] ∨ 8 ≤ length cs] as a premise (the smallest one).  The context
    slice is only read, at any fraction. *)
Definition wp_readOnly__recvAck_body :=
  ∀ (ext : ffi_syntax) (ffi : ffi_model) (ffi_interp0 : ffi_interp ffi)
    (Σ : gFunctors) (hG : heapGS Σ) (ffi_semantics0 : ffi_semantics ext ffi)
    (sem : go.Semantics) (package_sem : raft.Assumptions)
    (ro : loc) (r : readonly.t) (from : w64) (ctx : slice.t)
    (cs : list w8) (dq : dfrac),
  {{{ is_pkg_init raft ∗ "Hown" ∷ own_ReadOnly ro r ∗
      "Hctx" ∷ ctx ↦*{dq} cs ∗ "%Hlen" ∷ ⌜ cs = [] ∨ 8 ≤ length cs ⌝ }}}
    ro @! (go.PointerType raft.readOnly) @! "recvAck" #from #ctx
  {{{ RET #(); own_ReadOnly ro (readonly_recvAck r from cs) ∗ ctx ↦*{dq} cs }}}.

Module Type READONLY__RECVACK.
  Parameter wp_readOnly__recvAck : wp_readOnly__recvAck_body.
  Arguments wp_readOnly__recvAck {_ _ _ _ _ _ _ _}.
End READONLY__RECVACK.
