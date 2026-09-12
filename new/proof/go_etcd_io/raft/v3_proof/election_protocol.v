(** * Protocol-level model of etcd raft's leader election.

    This file is the specification side of the refinement proof in
    [New.proof.go_etcd_io.raft.v3_proof.election]: it defines the abstract
    state machine that a single raft node is supposed to implement, the
    ghost state [own_raft_ghost] representing a node's protocol state, the
    knowledge [is_message] attached to a message that has legitimately been
    put on the network, and the single fancy-update lemma connecting them.

    Scope.  Everything here (and the proofs in [election.v]) assumes:
      - no pre-vote            ([r.preVote = false]),
      - no check-quorum        ([r.checkQuorum = false]),
      - no proposals           (no [MsgProp] is ever stepped),
      - no read-only requests  (no [MsgReadIndex] is ever stepped),
      - no reconfiguration     (the voter set [cfg] is fixed, no learners).

    Under these assumptions the only thing a node's log contributes to
    election is the [isUpToDate] check, which can only make a node *decline*
    to vote.  Declining is always protocol-legal, so the log does not appear
    in this model at all: a node's protocol state is
    [(term, vote, lead, role, votes)].

    The point of the model is election safety — at most one leader per term —
    which is recorded as [is_leader_unique] below. *)

From RecordUpdate Require Import RecordSet.
Require Export New.proof.proof_prelude.
Import RecordSetNotations.

(** ** Abstract node state *)

Module role.
Inductive t := Follower | Candidate | Leader.
#[global] Instance eq_dec : EqDecision t.
Proof. solve_decision. Defined.
End role.

Module nstate.
Record t :=
  mk {
      term : w64;             (** [raft.Term] *)
      vote : w64;             (** [raft.Vote]; [W64 0] is the Go code's [None] *)
      lead : w64;             (** [raft.lead]; [W64 0] is the Go code's [None] *)
      role : role.t;          (** [raft.state] *)
      votes : gmap w64 bool;  (** [raft.trk.Votes] *)
    }.
#[global] Instance settable : Settable _ :=
  settable! mk <term; vote; lead; role; votes>.
End nstate.

(** ** Abstract messages

    Only the message types that matter for election appear.  [App] and
    [Heartbeat] are included because receiving one at a higher term makes the
    receiver step down *and* adopt the sender as leader, which is an election
    transition. *)

Module mtype.
Inductive t := Vote | VoteResp | App | Heartbeat.
#[global] Instance eq_dec : EqDecision t.
Proof. solve_decision. Defined.
End mtype.

Module msg.
Record t :=
  mk {
      ty : mtype.t;
      from : w64;
      to : w64;
      term : w64;
      reject : bool;
    }.
End msg.

(** Message types whose sender claims to be the leader of [term]. *)
Definition from_leader (ty : mtype.t) : bool :=
  match ty with mtype.App | mtype.Heartbeat => true | _ => false end.

Section model.

(** [cfg] is the (fixed) set of voters; [id] the node being described. *)
Context (cfg : gset w64) (id : w64).

Definition is_quorum (q : gset w64) : Prop := size cfg < 2 * size (q ∩ cfg).

Definition granted (votes : gmap w64 bool) : gset w64 :=
  dom (filter (λ '(_, v), v = true) votes).
Definition rejected (votes : gmap w64 bool) : gset w64 :=
  dom (filter (λ '(_, v), v = false) votes).

(** ** Role transitions

    These mirror the Go code exactly.  [reset(term)] clears [Vote] only when
    the term actually changes, always clears [lead] and the vote tally; the
    [becomeX] wrappers then set [lead] and [state]. *)

Definition become_follower (s : nstate.t) (term lead : w64) : nstate.t :=
  {| nstate.term := term;
     nstate.vote := if decide (term = s.(nstate.term))
                    then s.(nstate.vote) else W64 0;
     nstate.lead := lead;
     nstate.role := role.Follower;
     nstate.votes := ∅ |}.

Definition become_candidate (s : nstate.t) : nstate.t :=
  {| nstate.term := word.add s.(nstate.term) (W64 1);
     nstate.vote := id;
     nstate.lead := W64 0;
     nstate.role := role.Candidate;
     nstate.votes := ∅ |}.

Definition become_leader (s : nstate.t) : nstate.t :=
  {| nstate.term := s.(nstate.term);
     nstate.vote := s.(nstate.vote);
     nstate.lead := id;
     nstate.role := role.Leader;
     nstate.votes := ∅ |}.

(** [raft.trk.RecordVote]: the first vote recorded for a node wins; later
    ones are dropped. *)
Definition record_vote (votes : gmap w64 bool) (from : w64) (v : bool)
  : gmap w64 bool :=
  match votes !! from with Some _ => votes | None => <[from := v]> votes end.

(** A node may grant its vote to [from] in its current term when it has not
    already voted for somebody else and does not currently recognise a
    leader.  (The Go code additionally requires the candidate's log to be up
    to date, which can only turn a grant into a rejection; rejecting is
    always legal, so that check is invisible here.) *)
Definition can_vote (s : nstate.t) (from : w64) : Prop :=
  s.(nstate.vote) = from ∨ (s.(nstate.vote) = W64 0 ∧ s.(nstate.lead) = W64 0).

(** ** The transition relation

    [step s recv s' sent] says: a node in state [s], making use of the
    already-sent messages [recv], may move to state [s'] and put the
    messages [sent] on the network.

    Reflexivity and transitivity are part of the relation so that a single
    Go function which performs several protocol steps (e.g. [campaign],
    which becomes a candidate *and* broadcasts vote requests, or a
    [MsgVoteResp] that both records a vote and wins the election) refines a
    single [step]. *)

Inductive step : nstate.t → list msg.t → nstate.t → list msg.t → Prop :=
(** Structural rules. *)
| step_refl s :
  step s [] s []
| step_trans s₀ r₁ s₁ o₁ r₂ s₂ o₂ :
  step s₀ r₁ s₁ o₁ →
  step s₁ r₂ s₂ o₂ →
  step s₀ (r₁ ++ r₂) s₂ (o₁ ++ o₂)

(** [Step]'s term preamble: a message from a higher term makes the node step
    down.  It adopts the sender as leader exactly when the message is one
    only a leader sends. *)
| step_higher_term m s :
  uint.Z s.(nstate.term) < uint.Z m.(msg.term) →
  m.(msg.to) = id →
  step s [m]
       (become_follower s m.(msg.term)
          (if from_leader m.(msg.ty) then m.(msg.from) else W64 0))
       []

(** [hup] / [campaign]: a non-leader starts an election.  It increments its
    term, votes for itself, and sends a [MsgVote] to every other voter plus a
    self-addressed [MsgVoteResp] (which the Go code routes through
    [msgsAfterAppend]). *)
| step_campaign s peers :
  s.(nstate.role) ≠ role.Leader →
  id ∈ cfg →
  peers ≡ₚ elements (cfg ∖ {[id]}) →
  let s' := become_candidate s in
  step s []
       s'
       ([msg.mk mtype.VoteResp id id s'.(nstate.term) false] ++
        ((λ to, msg.mk mtype.Vote id to s'.(nstate.term) false) <$> peers))

(** Granting a vote. *)
| step_grant_vote m s :
  m.(msg.ty) = mtype.Vote →
  m.(msg.to) = id →
  m.(msg.term) = s.(nstate.term) →
  can_vote s m.(msg.from) →
  step s [m]
       (s <| nstate.vote := m.(msg.from) |>)
       [msg.mk mtype.VoteResp id m.(msg.from) s.(nstate.term) false]

(** Refusing a vote.  Always legal, so the Go code's extra conditions
    ([isUpToDate], and the [m.Term < r.Term] case which drops the message
    silently) are covered by this rule and by [step_refl]. *)
| step_reject_vote m s :
  m.(msg.ty) = mtype.Vote →
  m.(msg.to) = id →
  step s [m]
       s
       [msg.mk mtype.VoteResp id m.(msg.from) s.(nstate.term) true]

(** [stepCandidate] / [poll]: record a vote response for the current term. *)
| step_record_vote m s :
  m.(msg.ty) = mtype.VoteResp →
  m.(msg.to) = id →
  m.(msg.term) = s.(nstate.term) →
  s.(nstate.role) = role.Candidate →
  step s [m]
       (s <| nstate.votes :=
              record_vote s.(nstate.votes) m.(msg.from) (negb m.(msg.reject)) |>)
       []

(** Winning: a quorum of grants makes the candidate leader, and it
    immediately broadcasts an (empty) append. *)
| step_win s peers :
  s.(nstate.role) = role.Candidate →
  is_quorum (granted s.(nstate.votes)) →
  peers ≡ₚ elements (cfg ∖ {[id]}) →
  step s []
       (become_leader s)
       ((λ to, msg.mk mtype.App id to s.(nstate.term) false) <$> peers)

(** Losing: a quorum of rejections sends the candidate back to follower in
    the same term. *)
| step_lose s :
  s.(nstate.role) = role.Candidate →
  is_quorum (rejected s.(nstate.votes)) →
  step s [] (become_follower s s.(nstate.term) (W64 0)) []
.

End model.

(** ** Ghost state

    [own_raft_ghost γ id s] is exclusive ownership of node [id]'s protocol
    state; [is_message γ m] is the persistent knowledge that [m] was put on
    the network by a node following the protocol.

    These are axiomatized here.  Constructing them is the standard
    "authoritative map of node states + a set of sent messages, tied together
    by an invariant" development; what a client needs from that construction
    is exactly [own_raft_ghost_step] (the refinement obligation, which
    [election.v] discharges against the Go code) and [is_leader_unique] (the
    payoff). *)

Section ghost.
Context `{!invGS Σ}.

Axiom raft_election_names : Type.
Implicit Type γ : raft_election_names.

Axiom own_raft_ghost : ∀ γ (id : w64) (s : nstate.t), iProp Σ.
Axiom is_message : ∀ γ (m : msg.t), iProp Σ.

Axiom is_message_pers : ∀ γ m, Persistent (is_message γ m).
#[global] Existing Instance is_message_pers.

Axiom own_raft_ghost_timeless : ∀ γ id s, Timeless (own_raft_ghost γ id s).
#[global] Existing Instance own_raft_ghost_timeless.

Axiom own_raft_ghost_excl :
  ∀ γ id s1 s2, own_raft_ghost γ id s1 -∗ own_raft_ghost γ id s2 -∗ False.

(** The refinement obligation.  Any protocol-level transition of a single
    node — which may consume knowledge about messages already on the network
    and may put new messages on it — can be taken on the ghost state. *)
Axiom own_raft_ghost_step :
  ∀ γ (cfg : gset w64) (id : w64) s recv s' sent,
  step cfg id s recv s' sent →
  ([∗ list] m ∈ recv, is_message γ m) -∗
  own_raft_ghost γ id s ={⊤}=∗
  own_raft_ghost γ id s' ∗ ([∗ list] m ∈ sent, is_message γ m).

(** ** Election safety

    [is_leader γ id term] is the persistent fact that [id] was elected in
    [term].  That it is unique is what the whole model exists to provide. *)

Axiom is_leader : ∀ γ (id : w64) (term : w64), iProp Σ.
Axiom is_leader_pers : ∀ γ id term, Persistent (is_leader γ id term).
#[global] Existing Instance is_leader_pers.

Axiom own_raft_ghost_is_leader :
  ∀ γ id s,
  s.(nstate.role) = role.Leader →
  own_raft_ghost γ id s -∗ is_leader γ id s.(nstate.term).

Axiom is_leader_unique :
  ∀ γ id1 id2 term,
  is_leader γ id1 term -∗ is_leader γ id2 term -∗ ⌜ id1 = id2 ⌝.

End ghost.

(** ** Derived conveniences used by [election.v] *)

Section lemmas.
Context `{!invGS Σ}.
Implicit Type γ : raft_election_names.

(** Taking a step that consumes a single known message and sends none. *)
Lemma own_raft_ghost_step_1 γ cfg id s m s' :
  step cfg id s [m] s' [] →
  is_message γ m -∗
  own_raft_ghost γ id s ={⊤}=∗
  own_raft_ghost γ id s'.
Proof.
  iIntros (Hstep) "#Hm Hown".
  iMod (own_raft_ghost_step _ _ _ _ _ _ _ Hstep with "[] Hown") as "[$ _]".
  { by iFrame "#". }
  done.
Qed.

(** Taking a step that consumes nothing and sends nothing. *)
Lemma own_raft_ghost_step_0 γ cfg id s s' :
  step cfg id s [] s' [] →
  own_raft_ghost γ id s ={⊤}=∗ own_raft_ghost γ id s'.
Proof.
  iIntros (Hstep) "Hown".
  iMod (own_raft_ghost_step _ _ _ _ _ _ _ Hstep with "[] Hown") as "[$ _]".
  { done. }
  done.
Qed.

End lemmas.
