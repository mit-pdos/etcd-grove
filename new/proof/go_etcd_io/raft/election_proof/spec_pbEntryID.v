Require Export New.proof.go_etcd_io.raft.election_proof.inv_raft_phys.
Require Export New.proof.go_etcd_io.raft.election_proof.plog.

(** [pbEntryID(entry)] is the entry's id
    ([pbEntryIDⁱᵐᵖˡ], new/code/go_etcd_io/raft/v3.v:6897; types.go):

        func pbEntryID(entry *pb.Entry) entryID {
          return entryID{term: entry.Term, index: entry.Index}
        }

    One exit, no panic, no call.  It takes a *pointer*: every caller
    passes [&ents[i]] ([raftLog.findConflict], [logSlice.lastEntryID],
    [logSlice.valid]), so the triple reads the entry through a points-to
    at any fraction and gives it back.  The result is [plog.v]'s
    [ent_id]. *)
Definition wp_pbEntryID_body :=
  ∀ (ext : ffi_syntax) (ffi : ffi_model) (ffi_interp0 : ffi_interp ffi)
    (Σ : gFunctors) (hG : heapGS Σ) (ffi_semantics0 : ffi_semantics ext ffi)
    (sem : go.Semantics) (package_sem : raft.Assumptions)
    (p : loc) (dq : dfrac) (e : raftpb.Entry.t),
  {{{ is_pkg_init raft ∗ p ↦{dq} e }}}
    @! raft.pbEntryID #p
  {{{ RET #(ent_id e); p ↦{dq} e }}}.

Module Type PBENTRYID.
  Parameter wp_pbEntryID : wp_pbEntryID_body.
  Arguments wp_pbEntryID {_ _ _ _ _ _ _ _}.
End PBENTRYID.
