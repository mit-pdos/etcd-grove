Require Export New.proof.go_etcd_io.raft.election_proof.inv_raft_phys.
Require Export New.proof.go_etcd_io.raft.election_proof.step_lemmas.
(* [wp_Equal], for the MsgVote branch's Context comparison. *)
Require Export New.proof.bytes.

(** The top-level dispatch, and **one spec like every other function**.  The
    per-message-type branches are proof structure, not specification: since
    2026-09-17 they live in [proof_raft__Step_MsgHup.v], [_MsgVote.v] and
    [_MsgVoteResp.v] (and below those, [_MsgVote_gt.v], [_MsgVote_le.v],
    [_MsgVote_lt.v], [_MsgVote_eq_novote.v], [_MsgVote_eq_voted.v]), each a
    functor over [STEP_POSTULATES] with no [Module Type] and no [Parameter],
    so that [make -j] checks them in parallel.  Only [proof_raft__Step.v] and
    the combining files may [Require] one.  (An earlier version of this note
    said [Step] "is the one function with more than one spec"; that was
    written before the first cut's three per-message-type [Module Type]s were
    removed on 2026-09-14, and it is no longer true of anything here.)

    This is **the only spec in this development that mentions ghost state**.
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
  (* The ghost state is about one configuration, and it is this one.  Without
     this the caller could hand [own_raft_ghost_step] a [cfg] of its own
     choosing -- a singleton one, say, in which the node is its own quorum --
     and election safety would not hold.  See [raft_election_names]. *)
  γ.(re_cfg) = cfg →
  election_msg m →
  (* The node is a voter.  [stepCandidate] needs this outright (its [poll]
     and [becomeLeader] both do) and [spec_stepCandidate_MsgVoteResp.v] says
     to thread it in "from the caller" -- but [Step] *is* the outermost
     caller, so it has to enter the development here.  Under the no-learner,
     no-reconfiguration scope this is a property of the node, not of a
     particular call.  Added 2026-09-16 for the [MsgVoteResp] branch. *)
  id ∈ cfg →
  (* A [MsgHup] is local ([Term = 0]) and may start an election, which
     increments the term; [send] panics if that wraps to zero. *)
  (m.(raftpb.Message.Type') = MsgHup →
     m.(raftpb.Message.Term') = W64 0 ∧
     uint.Z s.(nstate.term) + 1 < 2 ^ 64) →
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
