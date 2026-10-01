Require Export New.proof.go_etcd_io.raft.election_proof.inv_raft_phys.
Require Export New.proof.go_etcd_io.raft.election_proof.plog.

(** [pbEntryID(entry)]: the id ([term], [index]) of the entry behind the
    pointer -- [ent_id] ([plog.v]).  Two field loads and a struct literal
    ([pbEntryIDⁱᵐᵖˡ], new/code/go_etcd_io/raft/v3.v:6897).  The entry is
    lent at any fraction: [findConflict] calls it on [&ents[i]] of a batch
    it holds read-only. *)
Definition wp_pbEntryID_body :=
  ∀ (ext : ffi_syntax) (ffi : ffi_model) (ffi_interp0 : ffi_interp ffi)
    (Σ : gFunctors) (hG : heapGS Σ) (ffi_semantics0 : ffi_semantics ext ffi)
    (sem : go.Semantics) (package_sem : raft.Assumptions)
    (p : loc) (dq : dfrac) (e : raftpb.Entry.t),
  {{{ is_pkg_init raft ∗ "He" ∷ p ↦{dq} e }}}
    @! raft.pbEntryID #p
  {{{ RET #(ent_id e); p ↦{dq} e }}}.

Module Type PBENTRYID.
  Parameter wp_pbEntryID : wp_pbEntryID_body.
  Arguments wp_pbEntryID {_ _ _ _ _ _ _ _}.
End PBENTRYID.
