(** * Spec: [raft.raft__Step_MsgVote]

    The single place this function's Hoare triple is written down.  The body
    carries all of its own binders, so the [Parameter] is a bare reference to
    it -- there is no second copy of the binder list to drift. *)

Require Export New.proof.go_etcd_io.raft.v3_proof.election.inv_raft_phys.

(** [MsgVote]: step down if the term is higher, then grant or decline. *)
Definition wp_raft__Step_MsgVote_body :=
  ∀ (ext : ffi_syntax) (ffi : ffi_model) (ffi_interp0 : ffi_interp ffi)
    (Σ : gFunctors) (hG : heapGS Σ) (ffi_semantics0 : ffi_semantics ext ffi)
    (sem : go.Semantics) (package_sem : raft.Assumptions)
    (bytes_sem : bytes.Assumptions)
    (cfg : gset w64)
    (γ : raft_election_names) (r : loc) (id : w64) (s : nstate.t) (m : raftpb.Message.t),
  m.(raftpb.Message.Type') = MsgVote →
  m.(raftpb.Message.To') = id →
  m.(raftpb.Message.Term') ≠ W64 0 →
  (* [send] stamps the sender's id into [From], and node ids are nonzero *)
  m.(raftpb.Message.From') ≠ W64 0 →
  {{{ is_pkg_init raft ∗
      "Hphys" ∷ own_raft_phys γ r id s ∗
      "Hghost" ∷ own_raft_ghost γ id s ∗
      "#Hm" ∷ is_message γ (abs_msg mtype.Vote m) ∗
      (* the message's [Context] is readable and is not the leader-transfer
         marker: leader transfer is out of scope *)
      "#Hctx" ∷ (∃ ctx, m.(raftpb.Message.Context') ↦*□ ctx ∗
                        ⌜ ctx ≠ campaignTransfer ⌝)
  }}}
    r @! (go.PointerType raft.raft) @! "Step" #m
  {{{ (err : error.t) s', RET #err;
      "Hphys" ∷ own_raft_phys γ r id s' ∗
      "Hghost" ∷ own_raft_ghost γ id s' ∗
      "%Hrefines" ∷ ⌜ ∃ recv sent,
          (∀ m', m' ∈ recv → m' = abs_msg mtype.Vote m) ∧
          step cfg id s recv s' sent ⌝ ∗
      "%Herr" ∷ ⌜ err = interface.nil ⌝ }}}.

Module Type STEP_MSGVOTE.
  Parameter wp_raft__Step_MsgVote : wp_raft__Step_MsgVote_body.
End STEP_MSGVOTE.
