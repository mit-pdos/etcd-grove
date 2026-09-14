(** * Spec: [raft.raft__Step_MsgVoteResp]

    The single place this function's Hoare triple is written down.  The body
    carries all of its own binders, so the [Parameter] is a bare reference to
    it -- there is no second copy of the binder list to drift. *)

Require Export New.proof.go_etcd_io.raft.v3_proof.election.inv_raft_phys.

(** [MsgVoteResp]: dispatched to [stepCandidate]. *)
Definition wp_raft__Step_MsgVoteResp_body :=
  ∀ (ext : ffi_syntax) (ffi : ffi_model) (ffi_interp0 : ffi_interp ffi)
    (Σ : gFunctors) (hG : heapGS Σ) (ffi_semantics0 : ffi_semantics ext ffi)
    (sem : go.Semantics) (package_sem : raft.Assumptions)
    (cfg : gset w64)
    (γ : raft_election_names) (r : loc) (id : w64) (s : nstate.t) (m : raftpb.Message.t),
  m.(raftpb.Message.Type') = MsgVoteResp →
  m.(raftpb.Message.To') = id →
  m.(raftpb.Message.Term') ≠ W64 0 →
  {{{ is_pkg_init raft ∗
      "Hphys" ∷ own_raft_phys γ r id s ∗
      "Hghost" ∷ own_raft_ghost γ id s ∗
      "#Hm" ∷ is_message γ (abs_msg mtype.VoteResp m)
  }}}
    r @! (go.PointerType raft.raft) @! "Step" #m
  {{{ (err : error.t) s', RET #err;
      "Hphys" ∷ own_raft_phys γ r id s' ∗
      "Hghost" ∷ own_raft_ghost γ id s' ∗
      "%Hrefines" ∷ ⌜ ∃ recv sent,
          (∀ m', m' ∈ recv → m' = abs_msg mtype.VoteResp m) ∧
          step cfg id s recv s' sent ⌝ ∗
      "%Herr" ∷ ⌜ err = interface.nil ⌝ }}}.

Module Type STEP_MSGVOTERESP.
  Parameter wp_raft__Step_MsgVoteResp : wp_raft__Step_MsgVoteResp_body.
End STEP_MSGVOTERESP.
