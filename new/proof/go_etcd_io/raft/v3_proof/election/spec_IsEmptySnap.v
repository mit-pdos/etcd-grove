Require Export New.proof.go_etcd_io.raft.v3_proof.election.inv_raft_phys.

(** [IsEmptySnap(sp)] ([IsEmptySnapⁱᵐᵖˡ], new/code/go_etcd_io/raft/v3.v:2004)
    is one field test:

      return sp.Metadata.Index == 0

    Pure, so the triple says exactly that.  It matters because
    [raft.maybeSendSnapshot] follows it with
    [panic("need non-empty snapshot")]: the proof there has to know the
    answer is [false], which it gets from [is_Storage]'s [HSnapshot]
    ([inv_storage.v]). *)
Definition wp_IsEmptySnap_body :=
  ∀ (ext : ffi_syntax) (ffi : ffi_model) (ffi_interp0 : ffi_interp ffi)
    (Σ : gFunctors) (hG : heapGS Σ) (ffi_semantics0 : ffi_semantics ext ffi)
    (sem : go.Semantics) (package_sem : raft.Assumptions)
    (sp : raftpb.Snapshot.t),
  {{{ is_pkg_init raft }}}
    @! raft.IsEmptySnap #sp
  {{{ (b : bool), RET #b;
      ⌜ b = bool_decide
              (sp.(raftpb.Snapshot.Metadata').(raftpb.SnapshotMetadata.Index')
               = W64 0) ⌝ }}}.

Module Type ISEMPTYSNAP.
  Parameter wp_IsEmptySnap : wp_IsEmptySnap_body.
  Arguments wp_IsEmptySnap {_ _ _ _ _ _ _ _}.
End ISEMPTYSNAP.
