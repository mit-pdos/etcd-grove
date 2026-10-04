Require Export New.proof.go_etcd_io.raft.election_proof.inv_raft_phys.

(** [ro.addRequest(commitIndex, req)] ([readOnly__addRequestⁱᵐᵖˡ],
    new/code/go_etcd_io/raft/v3.v:6250; [read_only.go:60]):

      ro.unconfirmedReads = append(ro.unconfirmedReads,
          &readIndexRequest{req: req, index: commitIndex})

    No panic, no call.  The queue is [own_ReadOnly]'s, a read-only slice
    with owned slack, so [append] writes into the slack or reallocates
    ([wp_slice_append_persistent]); the new request is allocated and
    persisted.  The record gains [readreq.mk commitIndex req.From ents]
    ([readonly_add]), where [ents] is what [req.Entries] points to, which
    the caller holds read-only (as [msg_abs] does for a queued message --
    the request message is stored by value, so its [Entries] slice is
    shared).  The receiver is a pointer, so the spec owns the object. *)
Definition wp_readOnly__addRequest_body :=
  ∀ (ext : ffi_syntax) (ffi : ffi_model) (ffi_interp0 : ffi_interp ffi)
    (Σ : gFunctors) (hG : heapGS Σ) (ffi_semantics0 : ffi_semantics ext ffi)
    (sem : go.Semantics) (package_sem : raft.Assumptions)
    (ro : loc) (r : readonly.t) (commitIndex : w64) (req : raftpb.Message.t)
    (ents : list raftpb.Entry.t),
  {{{ is_pkg_init raft ∗ "Hown" ∷ own_ReadOnly ro r ∗
      "#Hents" ∷ req.(raftpb.Message.Entries') ↦*□ ents }}}
    ro @! (go.PointerType raft.readOnly) @! "addRequest" #commitIndex #req
  {{{ RET #();
      own_ReadOnly ro (readonly_add r (readreq.mk commitIndex req.(raftpb.Message.From') ents)) }}}.

Module Type READONLY__ADDREQUEST.
  Parameter wp_readOnly__addRequest : wp_readOnly__addRequest_body.
  Arguments wp_readOnly__addRequest {_ _ _ _ _ _ _ _}.
End READONLY__ADDREQUEST.
