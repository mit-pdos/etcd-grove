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
      - no reconfiguration     (the voter set [cfg] is fixed, no learners),
      - **no configuration change is ever requested** -- so the log contains
        no [EntryConfChange] or [EntryConfChangeV2] entry, and
        [r.hasUnappliedConfChanges()] is always [false].  This is stronger
        than "the voter set is fixed": it is about what is in the log, not
        just about the resulting configuration, and it is what makes
        [hasUnappliedConfChanges] provable.  Its home once [own_raftLog] is a
        real definition is a conjunct there; see
        notes/raft-implementation-facts.md for why the function's early
        [return false] does not suffice.

    Under these assumptions the only thing a node's log contributes to
    election is the [isUpToDate] check, which can only make a node *decline*
    to vote.  Declining is always protocol-legal, so the log does not appear
    in this model at all: a node's protocol state is
    [(term, vote, lead, role, votes, outbox)].

    The point of the model is election safety — at most one leader per term —
    which is recorded as [is_leader_unique] below. *)

From RecordUpdate Require Import RecordSet.
From Perennial Require Import NamedProps.
Require Export New.proof.proof_prelude.
Import RecordSetNotations.

(** ** Roles *)

Module role.
Inductive t := Follower | Candidate | Leader.
#[global] Instance eq_dec : EqDecision t.
Proof. solve_decision. Defined.
End role.

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

(** ** Protocol node state

    [pstate.t] is the **protocol** state of one node: what the state machine
    below and the ghost state [own_raft_ghost] are about, and nothing more.
    It is *not* the abstraction [own_raft_phys] is indexed by -- that is the
    physical abstract state [nstate.t] ([election/defs.v]), which carries
    whatever the Go-level specs need (the [r.step] function, the progress
    map, a lent log page) on top of these fields.  The two are connected by
    [nstate_rel] ([election/defs.v]); [Step]'s spec is the one place that
    crosses from one to the other.  See notes/decisions.md, "Three layers".

    [outbox] is the node's pending outgoing messages — the abstraction of the
    Go code's two queues, [r.msgs] and [r.msgsAfterAppend], together.  Keeping
    it in the state rather than as a separate output of [step] is what lets
    "this function sent a message" be just "the outbox grew". *)

Module pstate.
Record t :=
  mk {
      term : w64;             (** [raft.Term] *)
      vote : w64;             (** [raft.Vote]; [W64 0] is the Go code's [None] *)
      lead : w64;             (** [raft.lead]; [W64 0] is the Go code's [None] *)
      role : role.t;          (** [raft.state] *)
      votes : gmap w64 bool;  (** [raft.trk.Votes] *)
      outbox : list msg.t;    (** [r.msgs] and [r.msgsAfterAppend], together *)
    }.
#[global] Instance settable : Settable _ :=
  settable! mk <term; vote; lead; role; votes; outbox>.
End pstate.

Section model.

(** [cfg] is the (fixed) set of voters; [id] the node being described. *)
Context (cfg : gset w64) (id : w64).

Definition is_quorum (q : gset w64) : Prop := size cfg < 2 * size (q ∩ cfg).

(** Two quorums meet.  This is the whole content of election safety; the same
    lemma, for the same [is_quorum], is proved in [readonly.v]. *)
Lemma quorums_intersect (q1 q2 : gset w64) :
  is_quorum q1 → is_quorum q2 → ∃ x, x ∈ q1 ∧ x ∈ q2.
Proof.
  intros Hsize1 Hsize2.
  destruct (decide (q1 ∩ q2 = ∅)) as [Hempty|Hne].
  2:{ apply set_choose_L in Hne as [x Hx]. exists x. set_solver. }
  exfalso.
  have Hunion : (q1 ∩ cfg) ∪ (q2 ∩ cfg) ⊆ cfg by set_solver.
  have Hdisj : (q1 ∩ cfg) ## (q2 ∩ cfg) by set_solver.
  apply subseteq_size in Hunion.
  rewrite size_union in Hunion; [|done].
  unfold is_quorum in *.
  lia.
Qed.

Definition granted (votes : gmap w64 bool) : gset w64 :=
  dom (filter (λ '(_, v), v = true) votes).
Definition rejected (votes : gmap w64 bool) : gset w64 :=
  dom (filter (λ '(_, v), v = false) votes).

(** Putting messages on the network. *)
Definition psend_msgs (s : pstate.t) (ms : list msg.t) : pstate.t :=
  s <| pstate.outbox := s.(pstate.outbox) ++ ms |>.

(** ** Role transitions

    These mirror the Go code exactly.  [reset(term)] clears [Vote] only when
    the term actually changes, always clears [lead] and the vote tally; the
    [becomeX] wrappers then set [lead] and [state].  None of them sends, so
    all three carry the outbox across unchanged. *)

Definition pbecome_follower (s : pstate.t) (term lead : w64) : pstate.t :=
  {| pstate.term := term;
     pstate.vote := if decide (term = s.(pstate.term))
                    then s.(pstate.vote) else W64 0;
     pstate.lead := lead;
     pstate.role := role.Follower;
     pstate.votes := ∅;
     pstate.outbox := s.(pstate.outbox) |}.

Definition pbecome_candidate (s : pstate.t) : pstate.t :=
  {| pstate.term := word.add s.(pstate.term) (W64 1);
     pstate.vote := id;
     pstate.lead := W64 0;
     pstate.role := role.Candidate;
     pstate.votes := ∅;
     pstate.outbox := s.(pstate.outbox) |}.

Definition pbecome_leader (s : pstate.t) : pstate.t :=
  {| pstate.term := s.(pstate.term);
     pstate.vote := s.(pstate.vote);
     pstate.lead := id;
     pstate.role := role.Leader;
     pstate.votes := ∅;
     pstate.outbox := s.(pstate.outbox) |}.

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
Definition pcan_vote (s : pstate.t) (from : w64) : Prop :=
  s.(pstate.vote) = from ∨ (s.(pstate.vote) = W64 0 ∧ s.(pstate.lead) = W64 0).

(** ** The transition relation

    [step s recv s'] says: a node in state [s], making use of the
    already-sent messages [recv], may move to state [s'].  Messages the node
    itself sends are not a separate output: they are the growth of
    [s'.(pstate.outbox)].

    Reflexivity and transitivity are part of the relation so that a single
    Go function which performs several protocol steps (e.g. [campaign],
    which becomes a candidate *and* broadcasts vote requests, or a
    [MsgVoteResp] that both records a vote and wins the election) refines a
    single [step]. *)

Inductive step : pstate.t → list msg.t → pstate.t → Prop :=
(** Structural rules. *)
| step_refl s :
  step s [] s
| step_trans s₀ r₁ s₁ r₂ s₂ :
  step s₀ r₁ s₁ →
  step s₁ r₂ s₂ →
  step s₀ (r₁ ++ r₂) s₂

(** [Step]'s term preamble: a message from a higher term makes the node step
    down.  It adopts the sender as leader exactly when the message is one
    only a leader sends. *)
| step_higher_term m s :
  uint.Z s.(pstate.term) < uint.Z m.(msg.term) →
  m.(msg.to) = id →
  step s [m]
       (pbecome_follower s m.(msg.term)
          (if from_leader m.(msg.ty) then m.(msg.from) else W64 0))

(** [hup] / [campaign]: a non-leader starts an election.  It increments its
    term, votes for itself, and sends a [MsgVote] to every other voter plus a
    self-addressed [MsgVoteResp] (which the Go code routes through
    [msgsAfterAppend]). *)
| step_campaign s peers :
  s.(pstate.role) ≠ role.Leader →
  id ∈ cfg →
  (** The term increments, and a term that wrapped round to one the node has
      already voted in would let it vote twice in that term -- which is
      exactly what election safety rests on not happening.  [Step]'s spec
      already carries this for a [MsgHup], because [send] panics on a zero
      term; here is where it is needed. *)
  uint.Z s.(pstate.term) + 1 < 2 ^ 64 →
  peers ≡ₚ elements (cfg ∖ {[id]}) →
  let s' := pbecome_candidate s in
  step s []
       (psend_msgs s'
          ([msg.mk mtype.VoteResp id id s'.(pstate.term) false] ++
           ((λ to, msg.mk mtype.Vote id to s'.(pstate.term) false) <$> peers)))

(** Granting a vote. *)
| step_grant_vote m s :
  m.(msg.ty) = mtype.Vote →
  m.(msg.to) = id →
  (** [W64 0] is the Go code's [None], so a vote *for* it is not a vote at
      all: [pstate.vote = W64 0] is how "has not voted this term" is written.
      Without this, granting to [W64 0] and then granting again would be two
      votes in one term.  [Step]'s spec already requires it of a [MsgVote]. *)
  m.(msg.from) ≠ W64 0 →
  m.(msg.term) = s.(pstate.term) →
  pcan_vote s m.(msg.from) →
  step s [m]
       (psend_msgs (s <| pstate.vote := m.(msg.from) |>)
          [msg.mk mtype.VoteResp id m.(msg.from) s.(pstate.term) false])

(** Refusing a vote.  Always legal, so the Go code's extra conditions
    ([isUpToDate], and the [m.Term < r.Term] case which drops the message
    silently) are covered by this rule and by [step_refl]. *)
| step_reject_vote m s :
  m.(msg.ty) = mtype.Vote →
  m.(msg.to) = id →
  step s [m]
       (psend_msgs s
          [msg.mk mtype.VoteResp id m.(msg.from) s.(pstate.term) true])

(** [stepCandidate] / [poll]: record a vote response for the current term. *)
| step_record_vote m s :
  m.(msg.ty) = mtype.VoteResp →
  m.(msg.to) = id →
  m.(msg.term) = s.(pstate.term) →
  s.(pstate.role) = role.Candidate →
  step s [m]
       (s <| pstate.votes :=
              record_vote s.(pstate.votes) m.(msg.from) (negb m.(msg.reject)) |>)

(** Winning: a quorum of grants makes the candidate leader, and it
    immediately broadcasts appends.

    The sends are deliberately loose: **any** list of [App] messages from
    [id] at the current term, including none at all.  An earlier version
    required exactly one per peer, i.e.
    [(λ to, msg.mk mtype.App id to s.(pstate.term) false) <$> peers] for
    [peers ≡ₚ elements (cfg ∖ {[id]})], and that is **not what the code
    does**: [bcastAppend] reaches [maybeSendAppend], which sends a [MsgApp]
    only when the log and the peer's [Progress] allow it, and otherwise
    sends a [MsgSnap] or nothing (the peer is paused, or there is nothing to
    send and [sendIfEmpty] is false).  Pinning the exact broadcast down
    would need the log and [Progress.State] to be non-opaque, which is log
    replication rather than election.

    Nothing is lost: election safety follows from quorum intersection on
    [votes], and no rule reads an [App]'s payload.  A receiver only ever
    uses an [App] through [step_higher_term], which cares about its term and
    that a leader sent it — both of which are still pinned here. *)
| step_win s ms :
  s.(pstate.role) = role.Candidate →
  is_quorum (granted s.(pstate.votes)) →
  Forall (λ m, m.(msg.ty) = mtype.App ∧ m.(msg.from) = id ∧
               m.(msg.term) = s.(pstate.term)) ms →
  step s [] (psend_msgs (pbecome_leader s) ms)

(** Losing: a quorum of rejections sends the candidate back to follower in
    the same term. *)
| step_lose s :
  s.(pstate.role) = role.Candidate →
  (** Go's [MajorityConfig.VoteResult] returns [VoteLost] when
      [votedCnt + missing < q], i.e. when the candidate **cannot still win** --
      not when a majority has rejected it.  The two differ, and the earlier
      premise [is_quorum (rejected s.(pstate.votes))] was therefore **false of
      the code**: with 4 voters, 2 rejecting and 2 yet to vote, the count is
      [0 + 2 < 3] so Go says [VoteLost], while the 2 rejections are not a
      quorum ([4 < 2*2] is false).

      Working the identity through:
      [votedCnt + missing = size cfg - size (rejected ∩ cfg)
                          = size (cfg ∖ rejected)], so
      [VoteLost ⇔ ¬ is_quorum (cfg ∖ rejected)] -- the voters who have *not*
      rejected are not a quorum.  That is what this premise now says.

      Weakening it is safe: [step_lose] moves a candidate to follower at the
      same term and creates no leader, so election safety is untouched. *)
  ¬ is_quorum (cfg ∖ rejected s.(pstate.votes)) →
  step s [] (pbecome_follower s s.(pstate.term) (W64 0))

(** [Ready] hands the pending messages to the transport, emptying the queues.
    Dropping messages from one's own outbox is always legal: the [is_message]
    facts handed out for them are persistent and survive.  [Ready] is out of
    scope for the election proof, but without this rule the model's outbox
    could only ever grow, which the physical state could not refine past
    the first drain. *)
| step_drain s o' :
  o' ⊆+ s.(pstate.outbox) →
  step s [] (s <| pstate.outbox := o' |>)
.

End model.

(** ** Ghost state

    The ghost state is deliberately *node-local*: there is no Iris invariant
    here and nothing global to open.  Each node owns the authority over its
    own vote history — which candidate it voted for in each term — and that
    authority is the exclusive part of [own_raft_ghost].  Everything a step
    needs to *learn* is persistent knowledge, so it can ride on a message or
    be held across a step with nowhere to put it.

    Three pieces:

    - [is_vote γ v term cand] — node [v] voted for [cand] in [term].  Frozen
      into [v]'s map when it is allocated, so it is persistent, and
      unforgeable because allocating it takes [v]'s own authority.
    - [is_message γ m] — what a legitimately sent message carries.  Only a
      *granting* [VoteResp] carries anything: the vote it reports.
    - [is_leader γ id term] — a quorum of [is_vote]s for [id] at [term].

    Election safety is then quorum intersection plus the agreement of two
    [is_vote]s for one node and term; that is all [is_leader_unique] is.

    What holds a node to one vote per term is [vote_hist_ok], the pure
    invariant inside [own_raft_ghost] tying the history to the current
    [(term, vote)]: the history mentions only terms the node has reached, and
    at the current term it agrees with [pstate.vote] — where [W64 0], the Go
    code's [None], means the term is absent from the history altogether.
    Every rule that clears [pstate.vote] raises [pstate.term] past everything
    in the history, which is exactly why [step_campaign] needs its no-wrap
    premise and [step_grant_vote] its [from ≠ 0]. *)

Record raft_election_names := {
    (** The voter set this ghost state is about.  It lives in [γ] rather than
        being a parameter of [own_raft_ghost_step]: a step free to choose its
        own [cfg] could choose a singleton one and elect itself, and the
        quorum [step_win] demands has to be a quorum of the same
        configuration [is_leader_unique] intersects in. *)
    re_cfg : gset w64;
    (** [re_votes !! id] names the ghost map holding node [id]'s vote
        history, [term ↦ candidate].  A node absent from here has no ghost
        state at all. *)
    re_votes : gmap w64 gname;
  }.

Section ghost.
Context `{!invGS Σ, !allG Σ}.

Implicit Type γ : raft_election_names.

(** *** Votes *)

Definition is_vote γ (v term cand : w64) : iProp Σ :=
  ∃ γv, ⌜ γ.(re_votes) !! v = Some γv ⌝ ∗ term ↪[γv]□ cand.

Global Instance is_vote_pers γ v term cand : Persistent (is_vote γ v term cand).
Proof. apply _. Qed.
Global Instance is_vote_timeless γ v term cand : Timeless (is_vote γ v term cand).
Proof. apply _. Qed.

(** One vote per node per term.  This is the other half of election safety. *)
Lemma is_vote_agree γ v term c1 c2 :
  is_vote γ v term c1 -∗ is_vote γ v term c2 -∗ ⌜ c1 = c2 ⌝.
Proof.
  iIntros "(%γ1 & %Hγ1 & H1) (%γ2 & %Hγ2 & H2)".
  rewrite Hγ1 in Hγ2. injection Hγ2 as <-.
  iApply (ghost_map_elem_agree with "H1 H2").
Qed.

(** *** Messages *)

Definition is_message γ (m : msg.t) : iProp Σ :=
  match m.(msg.ty) with
  | mtype.VoteResp =>
      if m.(msg.reject) then True%I
      else is_vote γ m.(msg.from) m.(msg.term) m.(msg.to)
  | _ => True%I
  end.

Global Instance is_message_pers γ m : Persistent (is_message γ m).
Proof.
  rewrite /is_message. destruct (m.(msg.ty)), (m.(msg.reject)); apply _.
Qed.
Global Instance is_message_timeless γ m : Timeless (is_message γ m).
Proof.
  rewrite /is_message. destruct (m.(msg.ty)), (m.(msg.reject)); apply _.
Qed.

(** Every message but a granting [VoteResp] is free. *)
Lemma is_message_triv γ m : m.(msg.ty) ≠ mtype.VoteResp → ⊢ is_message γ m.
Proof.
  rewrite /is_message. intros Hty. destruct (m.(msg.ty));
    [|congruence|..]; done.
Qed.

(** A *rejecting* [VoteResp] is free too: it reports no vote. *)
Lemma is_message_reject γ (from to term : w64) :
  ⊢ is_message γ (msg.mk mtype.VoteResp from to term true).
Proof. rewrite /is_message /=. done. Qed.

(** A granting [VoteResp] carries the vote it reports, and nothing else. *)
Lemma is_message_grant γ (from to term : w64) :
  is_vote γ from term to ⊢ is_message γ (msg.mk mtype.VoteResp from to term false).
Proof. by rewrite /is_message /=. Qed.

Lemma is_message_grant_inv γ m :
  m.(msg.ty) = mtype.VoteResp →
  m.(msg.reject) = false →
  is_message γ m -∗ is_vote γ m.(msg.from) m.(msg.term) m.(msg.to).
Proof. intros Hty Hrej. rewrite /is_message Hty Hrej. by iIntros "$". Qed.

(** *** Leadership *)

Definition is_leader γ (id term : w64) : iProp Σ :=
  ∃ q, ⌜ is_quorum γ.(re_cfg) q ⌝ ∗ [∗ set] v ∈ q, is_vote γ v term id.

Global Instance is_leader_pers γ id term : Persistent (is_leader γ id term).
Proof. apply _. Qed.
Global Instance is_leader_timeless γ id term : Timeless (is_leader γ id term).
Proof. apply _. Qed.

(** ** Election safety

    Two leaders in one term were each elected by a quorum; the quorums meet
    in a voter that cast one vote. *)
Lemma is_leader_unique γ id1 id2 term :
  is_leader γ id1 term -∗ is_leader γ id2 term -∗ ⌜ id1 = id2 ⌝.
Proof.
  iIntros "(%q1 & %Hq1 & #H1) (%q2 & %Hq2 & #H2)".
  destruct (quorums_intersect _ _ _ Hq1 Hq2) as (v & Hv1 & Hv2).
  iDestruct (big_sepS_elem_of _ _ _ Hv1 with "H1") as "Hv1".
  iDestruct (big_sepS_elem_of _ _ _ Hv2 with "H2") as "Hv2".
  iApply (is_vote_agree with "Hv1 Hv2").
Qed.

(** *** A node's protocol state *)

Definition vote_hist_ok (voted : gmap w64 w64) (s : pstate.t) : Prop :=
  (∀ t, is_Some (voted !! t) → uint.Z t ≤ uint.Z s.(pstate.term)) ∧
  voted !! s.(pstate.term) =
    (if decide (s.(pstate.vote) = W64 0) then None else Some s.(pstate.vote)).

(** [pbecome_follower] keeps the vote only when the term does not move.
    Rewriting with these before unfolding keeps the nested [decide] out of
    the goal, where [rewrite decide_False] would pick the wrong one. *)
Local Lemma pbecome_follower_vote_ne s term lead :
  term ≠ s.(pstate.term) → (pbecome_follower s term lead).(pstate.vote) = W64 0.
Proof. intros Hne. rewrite /pbecome_follower /=. rewrite decide_False //. Qed.

Local Lemma pbecome_follower_vote_same s lead :
  (pbecome_follower s s.(pstate.term) lead).(pstate.vote) = s.(pstate.vote).
Proof. rewrite /pbecome_follower /=. rewrite decide_True //. Qed.

(** A term the node has not reached yet is free to vote in. *)
Lemma vote_hist_fresh voted s t :
  vote_hist_ok voted s →
  uint.Z s.(pstate.term) < uint.Z t →
  voted !! t = None.
Proof.
  intros [Hdom _] Hlt. destruct (voted !! t) eqn:Ht; last done.
  exfalso. unshelve epose proof (Hdom t _) as Hle; [by eexists|]. lia.
Qed.

(** [vote_hist_ok] reads only [term] and [vote], so every rule that touches
    the outbox, the tally or the role preserves it by [reflexivity]. *)
Local Lemma vote_hist_ok_eq voted s1 s2 :
  vote_hist_ok voted s1 →
  s2.(pstate.term) = s1.(pstate.term) →
  s2.(pstate.vote) = s1.(pstate.vote) →
  vote_hist_ok voted s2.
Proof. rewrite /vote_hist_ok. intros H -> ->. exact H. Qed.

Definition leader_wit γ id s : iProp Σ :=
  match s.(pstate.role) with
  | role.Leader => is_leader γ id s.(pstate.term)
  | _ => True%I
  end.

Global Instance leader_wit_pers γ id s : Persistent (leader_wit γ id s).
Proof. rewrite /leader_wit. destruct (s.(pstate.role)); apply _. Qed.
Global Instance leader_wit_timeless γ id s : Timeless (leader_wit γ id s).
Proof. rewrite /leader_wit. destruct (s.(pstate.role)); apply _. Qed.

Definition own_raft_ghost γ (id : w64) (s : pstate.t) : iProp Σ :=
  ∃ γv voted,
    "%Hname"  ∷ ⌜ γ.(re_votes) !! id = Some γv ⌝ ∗
    "%Hidnz"  ∷ ⌜ id ≠ W64 0 ⌝ ∗
    "Hvoted"  ∷ ghost_map_auth γv 1 voted ∗
    "%Hhist"  ∷ ⌜ vote_hist_ok voted s ⌝ ∗
    "#Hfrags" ∷ ([∗ map] t ↦ c ∈ voted, is_vote γ id t c) ∗
    "#Hout"   ∷ ([∗ list] m ∈ s.(pstate.outbox), is_message γ m) ∗
    "#Htally" ∷ ([∗ set] v ∈ granted s.(pstate.votes), is_vote γ v s.(pstate.term) id) ∗
    "#Hlead"  ∷ leader_wit γ id s.

Global Instance own_raft_ghost_timeless γ id s : Timeless (own_raft_ghost γ id s).
Proof. apply _. Qed.

Lemma own_raft_ghost_intro γ id s γv voted :
  γ.(re_votes) !! id = Some γv →
  id ≠ W64 0 →
  ghost_map_auth γv 1 voted -∗
  ⌜ vote_hist_ok voted s ⌝ -∗
  ([∗ map] t ↦ c ∈ voted, is_vote γ id t c) -∗
  ([∗ list] m ∈ s.(pstate.outbox), is_message γ m) -∗
  ([∗ set] v ∈ granted s.(pstate.votes), is_vote γ v s.(pstate.term) id) -∗
  leader_wit γ id s -∗
  own_raft_ghost γ id s.
Proof.
  iIntros (??) "H1 %H2 #H3 #H4 #H5 #H6". iExists γv, voted. by iFrame "∗#%".
Qed.

Lemma own_raft_ghost_excl γ id s1 s2 :
  own_raft_ghost γ id s1 -∗ own_raft_ghost γ id s2 -∗ False.
Proof.
  iIntros "(%γ1 & %v1 & %Hn1 & _ & H1 & _) (%γ2 & %v2 & %Hn2 & _ & H2 & _)".
  rewrite Hn1 in Hn2. injection Hn2 as <-.
  iDestruct (ghost_map_auth_valid_2 with "H1 H2") as %[Hq _].
  exfalso. by apply Qp.not_add_le_l in Hq.
Qed.

(** Everything in a node's outbox was legitimately put there.  This is a plain
    entailment, not an update: [own_raft_ghost] carries the [is_message]s
    directly rather than deriving them from an invariant. *)
Lemma own_raft_ghost_outbox γ id s :
  own_raft_ghost γ id s -∗ ([∗ list] m ∈ s.(pstate.outbox), is_message γ m).
Proof. iIntros "(% & % & _ & _ & _ & _ & _ & #H & _)". iFrame "#". Qed.

Lemma own_raft_ghost_is_leader γ id s :
  s.(pstate.role) = role.Leader →
  own_raft_ghost γ id s -∗ is_leader γ id s.(pstate.term).
Proof.
  iIntros (Hrole) "(% & % & _ & _ & _ & _ & _ & _ & _ & #H)".
  rewrite /leader_wit Hrole. iFrame "#".
Qed.

(** *** Pure facts about the vote tally

    [granted] is a [dom] of a [filter], which nothing in stdpp reduces for
    us; these three are the only shapes the step proof needs. *)

Lemma elem_of_granted (votes : gmap w64 bool) v :
  v ∈ granted votes ↔ votes !! v = Some true.
Proof.
  rewrite /granted elem_of_dom. split.
  - intros [b Hb]. apply map_lookup_filter_Some in Hb as [Hv Hb].
    simpl in Hb. by subst.
  - intros Hv. eexists. apply map_lookup_filter_Some. done.
Qed.

Lemma granted_empty : granted ∅ = ∅.
Proof. rewrite /granted map_filter_empty dom_empty_L //. Qed.

Lemma elem_of_granted_record_vote votes from b v :
  v ∈ granted (record_vote votes from b) →
  v ∈ granted votes ∨ (v = from ∧ b = true).
Proof.
  rewrite /record_vote. destruct (votes !! from) eqn:Hf; first by left.
  rewrite !elem_of_granted. destruct (decide (v = from)) as [->|Hne].
  - rewrite lookup_insert_eq. intros [= ->]. by right.
  - assert (Hne' : from ≠ v) by congruence.
    rewrite lookup_insert_ne //. by left.
Qed.

(** *** The refinement obligation *)

Lemma own_raft_ghost_step γ (id : w64) s recv s' :
  step γ.(re_cfg) id s recv s' →
  ([∗ list] m ∈ recv, is_message γ m) -∗
  own_raft_ghost γ id s ={⊤}=∗
  own_raft_ghost γ id s'.
Proof.
  intros Hstep.
  induction Hstep as
    [ s
    | s0 r1 s1 r2 s2 Hst1 IH1 Hst2 IH2
    | m s Hlt Hto
    | s peers Hrole Hin Hnowrap Hperm
    | m s Hty Hto Hfrom Hterm Hcan
    | m s Hty Hto
    | m s Hty Hto Hterm Hrole
    | s ms Hrole Hq Hms
    | s Hrole Hnq
    | s o' Hsub ].

  - (* step_refl *)
    iIntros "_ Hown". by iFrame.

  - (* step_trans *)
    iIntros "Hrecv Hown".
    iEval (rewrite big_sepL_app) in "Hrecv".
    iDestruct "Hrecv" as "[Hr1 Hr2]".
    iMod (IH1 with "Hr1 Hown") as "Hown".
    by iMod (IH2 with "Hr2 Hown") as "$".

  - (* step_higher_term: a strictly greater term, so the vote is cleared and
       the new term is fresh in the history *)
    iIntros "_ Hown".
    iDestruct "Hown" as (γv voted)
      "(%Hname & %Hidnz & Hvoted & %Hhist & #Hfrags & #Hout & #Htally & #Hlead)".
    assert (Hne : m.(msg.term) ≠ s.(pstate.term)).
    { intros Heq. rewrite Heq in Hlt. lia. }
    pose proof Hhist as Hh; destruct Hh as [Hdom Heq].
    assert (Hhist' : vote_hist_ok voted (pbecome_follower s m.(msg.term)
                       (if from_leader m.(msg.ty) then m.(msg.from) else W64 0))).
    { rewrite /vote_hist_ok (pbecome_follower_vote_ne _ _ _ Hne).
      split.
      - simpl. intros t Ht. specialize (Hdom t Ht). lia.
      - simpl. rewrite ?decide_True //.
        eapply (vote_hist_fresh voted s); [exact Hhist|done]. }
    iModIntro.
    iApply (own_raft_ghost_intro _ _ _ γv voted Hname Hidnz
             with "Hvoted [] Hfrags [] [] []").
    + iPureIntro. exact Hhist'.
    + by rewrite /pbecome_follower /=.
    + rewrite /pbecome_follower /= granted_empty big_sepS_empty //.
    + rewrite /leader_wit /pbecome_follower /=. done.

  - (* step_campaign: the term goes up by one, so it is fresh, and the node
       votes for itself there *)
    iIntros "_ Hown".
    iDestruct "Hown" as (γv voted)
      "(%Hname & %Hidnz & Hvoted & %Hhist & #Hfrags & #Hout & #Htally & #Hlead)".
    set (t' := word.add s.(pstate.term) (W64 1)).
    assert (Ht' : uint.Z t' = uint.Z s.(pstate.term) + 1) by (subst t'; word).
    assert (Hcterm : (pbecome_candidate id s).(pstate.term) = t') by reflexivity.
    assert (Hcvote : (pbecome_candidate id s).(pstate.vote) = id) by reflexivity.
    assert (Hfree : voted !! t' = None).
    { eapply (vote_hist_fresh voted s); [done|lia]. }
    iMod (ghost_map_insert_persist t' id Hfree with "Hvoted") as "[Hvoted #Hself]".
    iAssert (is_vote γ id t' id) as "#Hisvote".
    { iExists γv. by iFrame "#". }
    assert (Hhist' : vote_hist_ok (<[t' := id]> voted) (pbecome_candidate id s)).
    { destruct Hhist as [Hdom _]. rewrite /vote_hist_ok Hcterm Hcvote. split.
      - intros t [c Hc]. destruct (decide (t = t')) as [->|Hne]; first lia.
        assert (Hne' : t' ≠ t) by congruence.
        rewrite lookup_insert_ne // in Hc.
        unshelve epose proof (Hdom t _) as Hle; [by eexists|]. lia.
      - rewrite lookup_insert_eq decide_False //. }
    iModIntro.
    iApply (own_raft_ghost_intro _ _ _ γv (<[t' := id]> voted) Hname Hidnz
             with "Hvoted [] [] [] [] []").
    + iPureIntro. apply (vote_hist_ok_eq _ _ _ Hhist'); reflexivity.
    + rewrite big_sepM_insert //. by iFrame "#".
    + rewrite /psend_msgs /pbecome_candidate /=.
      rewrite big_sepL_app. iSplitR; [iFrame "#"|].
      rewrite big_sepL_cons. iSplitR.
      * by iApply is_message_grant.
      * rewrite big_sepL_fmap. iApply big_sepL_intro.
        iIntros "!> %k %x %Hk". by iApply is_message_triv.
    + rewrite /psend_msgs /pbecome_candidate /= granted_empty big_sepS_empty //.
    + rewrite /leader_wit /psend_msgs /pbecome_candidate /=. done.

  - (* step_grant_vote: either the node has already voted this way, or the
       current term is free in the history *)
    iIntros "_ Hown".
    iDestruct "Hown" as (γv voted)
      "(%Hname & %Hidnz & Hvoted & %Hhist & #Hfrags & #Hout & #Htally & #Hlead)".
    iAssert (|==> ∃ voted', ghost_map_auth γv 1 voted' ∗
                  ⌜ vote_hist_ok voted' (s <| pstate.vote := m.(msg.from) |>) ⌝ ∗
                  ([∗ map] t ↦ c ∈ voted', is_vote γ id t c) ∗
                  is_vote γ id s.(pstate.term) m.(msg.from))%I
      with "[Hvoted]" as ">(%voted' & Hvoted & %Hhist' & #Hfrags' & #Hgrant)".
    { destruct Hcan as [Hsame | [Hnovote _]].
      - (* already voted for this candidate *)
        destruct Hhist as [Hdom Heq].
        assert (Hvnz : s.(pstate.vote) ≠ W64 0) by (rewrite Hsame; exact Hfrom).
        assert (Hlook : voted !! s.(pstate.term) = Some m.(msg.from)).
        { rewrite Heq decide_False //. by rewrite Hsame. }
        iExists voted. iFrame "Hvoted Hfrags".
        iDestruct (big_sepM_lookup _ _ _ _ Hlook with "Hfrags") as "#Hone".
        iFrame "Hone". iPureIntro.
        split; [exact Hdom|]. simpl. rewrite -Hsame. exact Heq.
      - (* first vote of this term *)
        assert (Hfree : voted !! s.(pstate.term) = None).
        { destruct Hhist as [_ Heq]. rewrite Heq decide_True //. }
        iMod (ghost_map_insert_persist s.(pstate.term) m.(msg.from) Hfree
               with "Hvoted") as "[Hvoted #Hnew]".
        iAssert (is_vote γ id s.(pstate.term) m.(msg.from)) as "#Hisvote".
        { iExists γv. by iFrame "#". }
        iModIntro. iExists (<[s.(pstate.term) := m.(msg.from)]> voted).
        iFrame "Hvoted Hisvote".
        iSplitR.
        + iPureIntro. destruct Hhist as [Hdom _]. split.
          * simpl. intros t [c Hc]. destruct (decide (t = s.(pstate.term)))
              as [->|Hne]; first lia.
            assert (Hne' : s.(pstate.term) ≠ t) by congruence.
            rewrite lookup_insert_ne // in Hc.
            unshelve epose proof (Hdom t _) as Hle; [by eexists|]. lia.
          * simpl. rewrite lookup_insert_eq decide_False //.
        + rewrite big_sepM_insert //. by iFrame "#". }
    iModIntro.
    iApply (own_raft_ghost_intro _ _ _ γv voted' Hname Hidnz
             with "Hvoted [] Hfrags' [] [] []").
    + iPureIntro. apply (vote_hist_ok_eq _ _ _ Hhist'); reflexivity.
    + rewrite /psend_msgs /=. rewrite big_sepL_app. iSplitR; [iFrame "#"|].
      rewrite big_sepL_singleton. by iApply is_message_grant.
    + rewrite /psend_msgs /=. iFrame "#".
    + rewrite /leader_wit /psend_msgs /=. iFrame "#".

  - (* step_reject_vote: a rejection carries nothing *)
    iIntros "_ Hown".
    iDestruct "Hown" as (γv voted)
      "(%Hname & %Hidnz & Hvoted & %Hhist & #Hfrags & #Hout & #Htally & #Hlead)".
    iModIntro.
    iApply (own_raft_ghost_intro _ _ _ γv voted Hname Hidnz
             with "Hvoted [] Hfrags [] [] []").
    + iPureIntro. apply (vote_hist_ok_eq _ _ _ Hhist); reflexivity.
    + rewrite /psend_msgs /=. rewrite big_sepL_app. iSplitR; [iFrame "#"|].
      rewrite big_sepL_singleton. by iApply is_message_reject.
    + rewrite /psend_msgs /=. iFrame "#".
    + rewrite /leader_wit /psend_msgs /=. iFrame "#".

  - (* step_record_vote: a granting response is backed by the voter's vote *)
    iIntros "Hrecv Hown".
    iDestruct "Hrecv" as "[#Hm _]".
    iDestruct "Hown" as (γv voted)
      "(%Hname & %Hidnz & Hvoted & %Hhist & #Hfrags & #Hout & #Htally & #Hlead)".
    iModIntro.
    iApply (own_raft_ghost_intro _ _ _ γv voted Hname Hidnz
             with "Hvoted [] Hfrags [] [] []").
    + iPureIntro. apply (vote_hist_ok_eq _ _ _ Hhist); reflexivity.
    + iFrame "#".
    + simpl. iApply big_sepS_intro. iIntros "!> %v %Hv".
      apply elem_of_granted_record_vote in Hv as [Hv | [-> Hb]].
      * by iApply (big_sepS_elem_of _ _ _ Hv with "Htally").
      * assert (Hrej : m.(msg.reject) = false)
          by (destruct (m.(msg.reject)); [discriminate Hb|reflexivity]).
        rewrite -Hterm -Hto.
        iApply (is_message_grant_inv γ m Hty Hrej with "Hm").
    + rewrite /leader_wit /=. iFrame "#".

  - (* step_win: the tally is the quorum that elected the node *)
    iIntros "_ Hown".
    iDestruct "Hown" as (γv voted)
      "(%Hname & %Hidnz & Hvoted & %Hhist & #Hfrags & #Hout & #Htally & #Hlead)".
    iAssert (is_leader γ id s.(pstate.term)) as "#Hnewlead".
    { iExists (granted s.(pstate.votes)). by iFrame "#". }
    iModIntro.
    iApply (own_raft_ghost_intro _ _ _ γv voted Hname Hidnz
             with "Hvoted [] Hfrags [] [] []").
    + iPureIntro. apply (vote_hist_ok_eq _ _ _ Hhist); reflexivity.
    + rewrite /psend_msgs /pbecome_leader /=. rewrite big_sepL_app.
      iSplitR; [iFrame "#"|].
      iApply big_sepL_intro. iIntros "!> %k %x %Hk".
      iApply is_message_triv.
      destruct (Forall_lookup_1 _ _ _ _ Hms Hk) as (Hty & _).
      rewrite Hty. done.
    + rewrite /psend_msgs /pbecome_leader /= granted_empty big_sepS_empty //.
    + rewrite /leader_wit /psend_msgs /pbecome_leader /=. iFrame "#".

  - (* step_lose: back to follower in the same term, so the vote stands *)
    iIntros "_ Hown".
    iDestruct "Hown" as (γv voted)
      "(%Hname & %Hidnz & Hvoted & %Hhist & #Hfrags & #Hout & #Htally & #Hlead)".
    assert (Hhist' : vote_hist_ok voted
                       (pbecome_follower s s.(pstate.term) (W64 0))).
    { destruct Hhist as [Hdom Heq].
      rewrite /vote_hist_ok pbecome_follower_vote_same.
      split; simpl; [done|exact Heq]. }
    iModIntro.
    iApply (own_raft_ghost_intro _ _ _ γv voted Hname Hidnz
             with "Hvoted [] Hfrags [] [] []").
    + iPureIntro. exact Hhist'.
    + by rewrite /pbecome_follower /=.
    + rewrite /pbecome_follower /= granted_empty big_sepS_empty //.
    + rewrite /leader_wit /pbecome_follower /=. done.

  - (* step_drain: the messages kept are messages that were there *)
    iIntros "_ Hown".
    iDestruct "Hown" as (γv voted)
      "(%Hname & %Hidnz & Hvoted & %Hhist & #Hfrags & #Hout & #Htally & #Hlead)".
    iModIntro.
    iApply (own_raft_ghost_intro _ _ _ γv voted Hname Hidnz
             with "Hvoted [] Hfrags [] [] []").
    + iPureIntro. apply (vote_hist_ok_eq _ _ _ Hhist); reflexivity.
    + simpl. iApply big_sepL_intro. iIntros "!> %k %x %Hk".
      iApply (big_sepL_elem_of with "Hout").
      eapply elem_of_submseteq; [by eapply list_elem_of_lookup_2|done].
    + simpl. iFrame "#".
    + rewrite /leader_wit /=. iFrame "#".
Qed.

(** *** Allocation

    Nothing above says the ghost state is inhabited, and an empty
    [own_raft_ghost] would make every lemma here true and useless.  This is
    what rules that out: a fresh ghost state for any set of nodes, each in the
    initial protocol state. *)

Definition init_pstate : pstate.t :=
  {| pstate.term := W64 0; pstate.vote := W64 0; pstate.lead := W64 0;
     pstate.role := role.Follower; pstate.votes := ∅; pstate.outbox := [] |}.

Local Lemma alloc_vote_maps (ids : gset w64) :
  ⊢ |==> ∃ (names : gmap w64 gname), ⌜ dom names = ids ⌝ ∗
      [∗ map] γv ∈ names, ghost_map_auth γv 1 (∅ : gmap w64 w64).
Proof.
  induction ids as [|x ids Hx IH] using set_ind_L.
  - iModIntro. iExists ∅. rewrite dom_empty_L big_sepM_empty. done.
  - iMod IH as (names Hdom) "Hm".
    iMod (ghost_map_alloc_empty (K:=w64) (V:=w64)) as (γv) "Hauth".
    iModIntro. iExists (<[x := γv]> names).
    rewrite dom_insert_L Hdom. iSplit; first done.
    rewrite big_sepM_insert; [by iFrame|].
    by apply not_elem_of_dom; rewrite Hdom.
Qed.

Lemma own_raft_ghost_alloc (cfg : gset w64) (ids : gset w64) :
  W64 0 ∉ ids →
  ⊢ |==> ∃ γ, ⌜ γ.(re_cfg) = cfg ⌝ ∗
      [∗ set] id ∈ ids, own_raft_ghost γ id init_pstate.
Proof.
  iIntros (Hnz).
  iMod (alloc_vote_maps ids) as (names Hdom) "Hm".
  iModIntro. iExists {| re_cfg := cfg; re_votes := names |}.
  iSplit; first done.
  rewrite -Hdom -big_sepM_dom.
  iApply (big_sepM_impl with "Hm").
  iIntros "!> %id %γv %Hlook Hauth".
  iExists γv, ∅.
  iSplit; first done.
  iSplit.
  { iPureIntro. intros ->. apply Hnz. rewrite -Hdom. by apply elem_of_dom. }
  iFrame "Hauth".
  iSplit.
  { iPureIntro. split; [by intros t []|]. rewrite lookup_empty //. }
  rewrite big_sepM_empty big_sepL_nil granted_empty big_sepS_empty.
  rewrite /leader_wit /=.
  iSplit; first done. iSplit; first done. iSplit; first done.
  done.
Qed.

End ghost.

(** ** Derived conveniences used by [election.v] *)

Section lemmas.
Context `{!invGS Σ, !allG Σ}.
Implicit Type γ : raft_election_names.

(** Taking a step that consumes a single known message. *)
Lemma own_raft_ghost_step_1 γ id s m s' :
  step γ.(re_cfg) id s [m] s' →
  is_message γ m -∗
  own_raft_ghost γ id s ={⊤}=∗
  own_raft_ghost γ id s'.
Proof.
  iIntros (Hstep) "#Hm Hown".
  iMod (own_raft_ghost_step _ _ _ _ _ Hstep with "[] Hown") as "$".
  { by iFrame "#". }
  done.
Qed.

(** Taking a step that consumes nothing. *)
Lemma own_raft_ghost_step_0 γ id s s' :
  step γ.(re_cfg) id s [] s' →
  own_raft_ghost γ id s ={⊤}=∗ own_raft_ghost γ id s'.
Proof.
  iIntros (Hstep) "Hown".
  iMod (own_raft_ghost_step _ _ _ _ _ Hstep with "[] Hown") as "$".
  { done. }
  done.
Qed.

End lemmas.
