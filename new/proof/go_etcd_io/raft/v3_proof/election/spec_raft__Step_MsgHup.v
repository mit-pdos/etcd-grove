(** * Spec: [raft.raft__Step_MsgHup]

    The single place this function's Hoare triple is written down.  The body
    carries all of its own binders, so the [Parameter] is a bare reference to
    it -- there is no second copy of the binder list to drift. *)

Require Export New.proof.go_etcd_io.raft.v3_proof.election.inv_raft_phys.

(** [MsgHup] is a local message ([m.Term = 0]), so [Step]'s term preamble is
    skipped entirely and it goes straight to [hup]. *)
Definition wp_raft__Step_MsgHup_body :=
  ∀ (ext : ffi_syntax) (ffi : ffi_model) (ffi_interp0 : ffi_interp ffi)
    (Σ : gFunctors) (hG : heapGS Σ) (ffi_semantics0 : ffi_semantics ext ffi)
    (sem : go.Semantics) (package_sem : raft.Assumptions)
    (cfg : gset w64)
    (γ : raft_election_names) (r : loc) (id : w64) (s : nstate.t) (m : raftpb.Message.t),
  m.(raftpb.Message.Type') = MsgHup →
  m.(raftpb.Message.Term') = W64 0 →
  {{{ is_pkg_init raft ∗
      "Hphys" ∷ own_raft_phys γ r id s ∗
      "Hghost" ∷ own_raft_ghost γ id s
  }}}
    r @! (go.PointerType raft.raft) @! "Step" #m
  {{{ (err : error.t) s', RET #err;
      "Hphys" ∷ own_raft_phys γ r id s' ∗
      "Hghost" ∷ own_raft_ghost γ id s' ∗
      "%Hrefines" ∷ ⌜ ∃ sent, step cfg id s [] s' sent ⌝ ∗
      "%Herr" ∷ ⌜ err = interface.nil ⌝ }}}.

Module Type STEP_MSGHUP.
  Parameter wp_raft__Step_MsgHup : wp_raft__Step_MsgHup_body.
End STEP_MSGHUP.
