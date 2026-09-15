(** * Physical ownership of the raft struct *)

Require Export New.proof.go_etcd_io.raft.v3_proof.election.inv_raftlog.
Require Export New.proof.go_etcd_io.raft.v3_proof.election.inv_tracker.
Require Export New.proof.go_etcd_io.raft.v3_proof.election.inv_logger.
Require Export New.proof.go_etcd_io.raft.v3_proof.election.inv_misc.

(** Step over one logging call: build the variadic argument slice, then
    apply the logger spec.  Expects [is_Logger] under the name [Hlogger]. *)
Ltac wp_log lok_eq :=
  wp_apply wp_slice_literal;
  [ iSplitR;
    [ done
    | iIntros "% [? _]"; try wp_auto; rewrite lok_eq; try wp_auto;
      wp_apply (wp_Logger__logf with "Hlogger") as "_";
      [ rewrite /log_methods; set_solver | ] ] ].

Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : raft.Assumptions}.
Collection W := sem + package_sem.
Set Default Proof Using "W".

Implicit Type γ : raft_election_names.
Implicit Type s : nstate.t.

(** [m] is a message this node is allowed to have put on the network. *)
Definition is_phys_msg γ (m : raftpb.Message.t) : iProp Σ :=
  ∃ ty, ⌜ mtype_of m.(raftpb.Message.Type') = Some ty ⌝ ∗
        is_message γ (abs_msg ty m).

#[global] Instance is_phys_msg_pers γ m : Persistent (is_phys_msg γ m).
Proof. apply _. Qed.

(** ** Physical ownership of the raft struct

    [own_raft_phys γ r id s] is full ownership of the [raft] struct at [r],
    in a state that refines the protocol state [s], and whose two outgoing
    message queues contain only messages [γ] certifies as protocol-legal. *)
Definition own_raft_phys γ (r : loc) (id : w64) s : iProp Σ :=
  ∃ (rv : raft.raft.t) (msgs msgsAA : list raftpb.Message.t)
    (lok : interface.t_ok),
  "Hr" ∷ r ↦ rv ∗

  (** the abstraction relation *)
  "%Hid" ∷ ⌜ rv.(raft.raft.id') = id ⌝ ∗
  "%Hterm" ∷ ⌜ rv.(raft.raft.Term') = s.(nstate.term) ⌝ ∗
  "%Hvote" ∷ ⌜ rv.(raft.raft.Vote') = s.(nstate.vote) ⌝ ∗
  "%Hlead" ∷ ⌜ rv.(raft.raft.lead') = s.(nstate.lead) ⌝ ∗
  "%Hstate" ∷ ⌜ rv.(raft.raft.state') = state_w64 s.(nstate.role) ⌝ ∗

  (** the vote tally, and the rest of the heap the tracker points at.  The
      tracker's own bytes are covered by [Hr] above, since [trk] is embedded
      by value; this is only what hangs off it. *)
  "Htrk" ∷ own_tracker rv.(raft.raft.trk') s.(nstate.votes) ∗

  (** the log, opaque *)
  "Hlog" ∷ own_raftLog rv.(raft.raft.raftLog') ∗

  (** outgoing messages.  [send] routes vote/append *responses* to
      [msgsAfterAppend] and everything else to [msgs]; both must only ever
      hold protocol-legal messages. *)
  "Hmsgs" ∷ rv.(raft.raft.msgs') ↦* msgs ∗
  "Hmsgs_cap" ∷ own_slice_cap raftpb.Message.t rv.(raft.raft.msgs') (DfracOwn 1) ∗
  "HmsgsAA" ∷ rv.(raft.raft.msgsAfterAppend') ↦* msgsAA ∗
  "HmsgsAA_cap" ∷ own_slice_cap raftpb.Message.t
                    rv.(raft.raft.msgsAfterAppend') (DfracOwn 1) ∗
  "#Hsent" ∷ ([∗ list] m ∈ msgs, is_phys_msg γ m) ∗
  "#HsentAA" ∷ ([∗ list] m ∈ msgsAA, is_phys_msg γ m) ∗

  (** scope assumptions *)
  "%HnoPreVote" ∷ ⌜ rv.(raft.raft.preVote') = false ⌝ ∗
  "%HnoCheckQuorum" ∷ ⌜ rv.(raft.raft.checkQuorum') = false ⌝ ∗
  "%HnoLearner" ∷ ⌜ rv.(raft.raft.isLearner') = false ⌝ ∗
  "%HnoTransfer" ∷ ⌜ rv.(raft.raft.leadTransferee') = W64 0 ⌝ ∗
  "%Hid_nz" ∷ ⌜ id ≠ W64 0 ⌝ ∗

  (** logging, tracing, and everything else *)
  "%Hlok" ∷ ⌜ rv.(raft.raft.logger') = interface.ok lok ⌝ ∗
  "#Hlogger" ∷ is_Logger lok ∗
  "Hmisc" ∷ own_raft_misc rv.(raft.raft.readStates') rv.(raft.raft.readOnly')
             rv.(raft.raft.pendingReadIndexMessages').

(** The step function stored in [r.step] is determined by the role; rather
    than naming the closure, we record which of the three [stepX] functions
    it is by the role, and dispatch on the role at the one call site. *)

End proof.
