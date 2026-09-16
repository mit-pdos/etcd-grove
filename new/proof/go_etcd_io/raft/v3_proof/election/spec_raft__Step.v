Require Export New.proof.go_etcd_io.raft.v3_proof.election.inv_raft_phys.
Require Export New.proof.go_etcd_io.raft.v3_proof.election.step_lemmas.
(* [wp_Equal], for the MsgVote branch's Context comparison. *)
Require Export New.proof.bytes.

(** The top-level dispatch.  NOTE: [Step] is the one function with more than
    one spec -- the three per-message-type theorems above are a layering of the
    same Go function, not a duplicate specification of it.

    It is also **the only spec in this development that mentions ghost state**.
    Every function below it is specified against [own_raft_phys] alone, saying
    which state the struct ends up refining and how the outbox grew; [Step]
    assembles those pure facts into one [step] witness and takes one
    [own_raft_ghost_step].  A caller that needs to know a pending outgoing
    message is protocol-legal gets that from [own_raft_ghost_outbox], not from
    [own_raft_phys]. *)
Definition wp_raft__Step_body :=
  ∀ (ext : ffi_syntax) (ffi : ffi_model) (ffi_interp0 : ffi_interp ffi)
    (Σ : gFunctors) (hG : heapGS Σ) (ffi_semantics0 : ffi_semantics ext ffi)
    (sem : go.Semantics) (package_sem : raft.Assumptions)
    (cfg : gset w64)
    (γ : raft_election_names) (r : loc) (id : w64) (s : nstate.t) (m : raftpb.Message.t),
  election_msg m →
  (m.(raftpb.Message.Type') = MsgHup → m.(raftpb.Message.Term') = W64 0) →
  (m.(raftpb.Message.Type') = MsgVote →
     m.(raftpb.Message.To') = id ∧ m.(raftpb.Message.Term') ≠ W64 0 ∧
     m.(raftpb.Message.From') ≠ W64 0) →
  (m.(raftpb.Message.Type') = MsgVoteResp →
     m.(raftpb.Message.To') = id ∧ m.(raftpb.Message.Term') ≠ W64 0) →
  {{{ is_pkg_init raft ∗
      "Hphys" ∷ own_raft_phys cfg r id s ∗
      "Hghost" ∷ own_raft_ghost γ id s ∗
      "#Hm" ∷ (∀ ty, ⌜ mtype_of m.(raftpb.Message.Type') = Some ty ⌝ -∗
                     is_message γ (abs_msg ty m)) ∗
      "#Hctx" ∷ (∃ ctx, m.(raftpb.Message.Context') ↦*□ ctx ∗
                        ⌜ ctx ≠ campaignTransfer ⌝)
  }}}
    r @! (go.PointerType raft.raft) @! "Step" #m
  {{{ (err : error.t) s', RET #err;
      "Hphys" ∷ own_raft_phys cfg r id s' ∗
      "Hghost" ∷ own_raft_ghost γ id s' ∗
      "%Hrefines" ∷ ⌜ ∃ recv, step cfg id s recv s' ⌝ ∗
      "%Herr" ∷ ⌜ err = interface.nil ⌝ }}}.

Module Type STEP.
  Parameter wp_raft__Step : wp_raft__Step_body.
  Arguments wp_raft__Step {_ _ _ _ _ _ _ _}.
End STEP.
