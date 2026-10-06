Require Export New.proof.go_etcd_io.raft.election_proof.spec_raft__Step.

(** * [RawNode.Propose] (rawnode.go:90), the client's entry point

    [Propose(data)] is one call: [rn.raft.Step(pb.Message{Type: MsgProp,
    From: rn.raft.id, Entries: []pb.Entry{{Data: data}}})] -- a one-entry
    batch whose entry is the zero [Entry] but for [Data]
    ([prop_entry data_sl]).  So its spec is [Step]'s [MsgProp] arm
    ([spec_raft__Step.v]) for that batch and one proposal update:

    - the client hands in [prop_au γ e0 Q] ([protocol.v], "The proposal
      registry"): an update of the global committed log that runs when the
      entry, stamped at some [(t, i)], is committed, with result [Q t i];
    - appended at the leader (the node is the leader and [appendEntry]
      accepted it), the update is registered at the entry's [(term,
      index)] -- [ps]'s term and the index after [ps]'s last -- and the
      client gets [is_prop] and the token [prop_tok], which it trades for
      [Q t i] with [prop_collect] once [is_committed] shows an entry of
      term [t] at [i];
    - otherwise -- forwarded to the leader by a follower ([err = nil]), or
      dropped ([ErrProposalDropped]: no leader known, a candidate, the
      leader refused it) -- the update comes back unrun.  A forwarded
      proposal is not tracked: when the leader appends it, the update is
      not there (the forwarded [MsgProp] carries no ghost state).

    **The [RawNode] is taken raw** (2026-10-06): the points-to of the
    struct at [rn], whose [raft] field is [r], next to [own_raft_phys] of
    [r] and the ghost state.  To be folded into [own_RawNode] (being
    written on another branch, [inv_rawnode.v]) when that lands.

    [From: rn.raft.id] is why [Step]'s [MsgProp] premise and [send]'s
    [From] premise admit [From = id] since 2026-10-06. *)

(** The entry [Propose] builds: [pb.Entry{Data: data}]. *)
Definition prop_entry (data_sl : slice.t) : raftpb.Entry.t :=
  zero_val raftpb.Entry.t <| raftpb.Entry.Data' := data_sl |>.

Definition wp_RawNode__Propose_body :=
  ∀ (ext : ffi_syntax) (ffi : ffi_model) (ffi_interp0 : ffi_interp ffi)
    (Σ : gFunctors) (hG : heapGS Σ) (ffi_semantics0 : ffi_semantics ext ffi)
    (sem : go.Semantics) (package_sem : raft.Assumptions)
    (cfg : gset w64) (γ : raft_election_names)
    (rn : loc) (rnv : raft.RawNode.t) (r : loc) (id : w64)
    (s : nstate.t) (ps : pstate.t)
    (data_sl : slice.t) (data : list w8) (Q : w64 → w64 → iProp Σ),
  (* [Step]'s premises that are not about the message *)
  γ.(re_cfg) = cfg →
  id ∈ cfg →
  nstate_rel s ps →
  rnv.(raft.RawNode.raft') = r →
  {{{ is_pkg_init raft ∗
      (* to become [own_RawNode] (see above) *)
      "Hrn" ∷ rn ↦ rnv ∗
      "Hphys" ∷ own_raft_phys cfg r id s ∗
      "Hghost" ∷ own_raft_ghost γ id ps ∗
      "#Hdata" ∷ data_sl ↦*□ data ∗
      "Hau" ∷ prop_au γ (prop_entry data_sl) Q }}}
    rn @! (go.PointerType raft.RawNode) @! "Propose" #data_sl
  {{{ (err : error.t) s' ps', RET #err;
      "Hrn" ∷ rn ↦ rnv ∗
      "Hphys" ∷ own_raft_phys cfg r id s' ∗
      "Hghost" ∷ own_raft_ghost γ id ps' ∗
      "%Hrel" ∷ ⌜ nstate_rel s' ps' ⌝ ∗
      "%Hrefines" ∷ ⌜ ∃ recv, step cfg id ps recv ps' ⌝ ∗
      "Hres" ∷ (
        (* appended at the leader: registered at [(ps.term, last + 1)] *)
        (⌜ err = interface.nil ∧ ps.(pstate.role) = role.Leader ⌝ ∗
         ∃ γp, is_prop γ ps.(pstate.term) (word.add (plast_index ps) (W64 1)) γp Q ∗
               prop_tok γp)
        (* forwarded or dropped: the update back *)
      ∨ (prop_au γ (prop_entry data_sl) Q ∗
         (⌜ err = interface.nil ⌝ ∨ (global_addr raft.ErrProposalDropped) ↦□ err))) }}}.

Module Type RAWNODE__PROPOSE.
  Parameter wp_RawNode__Propose : wp_RawNode__Propose_body.
  Arguments wp_RawNode__Propose {_ _ _ _ _ _ _ _}.
End RAWNODE__PROPOSE.
