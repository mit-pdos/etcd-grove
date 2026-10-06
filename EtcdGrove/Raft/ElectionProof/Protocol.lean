/-
Port of `election_proof/protocol.v`: the protocol-level model of etcd raft's leader
election.

This file is the specification side of the refinement proof in `Election.lean`: it
defines the abstract state machine that a single raft node is supposed to implement,
the ghost state `ownRaftGhost` representing a node's protocol state, the knowledge
`IsMessage` attached to a message that has legitimately been put on the network, and
the single fancy-update lemma connecting them.

Scope. Everything here (and the proofs in `Election.lean`) assumes:
* no pre-vote (`r.preVote = false`),
* no check-quorum (`r.checkQuorum = false`),
* no proposals (no `MsgProp` is ever stepped),
* no read-only requests (no `MsgReadIndex` is ever stepped),
* no reconfiguration (the voter set `cfg` is fixed, no learners),
* **no configuration change is ever requested** -- so the log contains no
  `EntryConfChange` or `EntryConfChangeV2` entry, and `r.hasUnappliedConfChanges()`
  is always `false`. This is stronger than "the voter set is fixed": it is about
  what is in the log, not just about the resulting configuration, and it is what
  makes `hasUnappliedConfChanges` provable (see main's
  notes/raft-implementation-facts.md for why the function's early `return false`
  does not suffice).

Under these assumptions the only thing a node's log contributes to election is the
`isUpToDate` check, which can only make a node *decline* to vote. Declining is always
protocol-legal, so the log does not appear in this model at all: a node's protocol
state is `(term, vote, lead, role, votes, outbox)`.

The model exists to make a spec of raft's *code* say something: `Election.lean`'s
`raft.wp_Step` is a triple about a Go function, and what lifts it above "the struct
fields changed" is that the states it moves between are states of this machine. That
the machine entails election safety — at most one leader per term, recorded as
`isLeader_unique` below — is the check that it was not defined into triviality, not
the result. See main's notes/decisions.md, 2026-09-21.

Lean notes: the message fields Rocq calls `from`/`to` (a Lean keyword and a common
name) are `src`/`dst`; the Rocq modules `role`, `mtype`, `msg`, `pstate` are the types
`Role`, `MsgType`, `Msg`, `PState`.
-/
import Perennial.Proof.ProofPrelude
import Perennial.Ghost.GhostMap

set_option autoImplicit false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI GMap

/-! ## Roles -/

inductive Role where
  | follower | candidate | leader
  deriving DecidableEq, Inhabited

/-! ## Abstract messages

Only the message types that matter for election appear. `app` and `heartbeat` are
included because receiving one at a higher term makes the receiver step down *and*
adopt the sender as leader, which is an election transition. -/

inductive MsgType where
  | vote | voteResp | app | heartbeat
  deriving DecidableEq, Inhabited

structure Msg where
  ty : MsgType
  /-- the sender (Go `m.From`) -/
  src : w64
  /-- the receiver (Go `m.To`) -/
  dst : w64
  term : w64
  reject : Bool
  deriving DecidableEq, Inhabited

/-- Message types whose sender claims to be the leader of `term`. -/
def fromLeader : MsgType → Bool
  | .app | .heartbeat => true
  | _ => false

/-! ## Protocol node state

`PState` is the **protocol** state of one node: what the state machine below and the
ghost state `ownRaftGhost` are about, and nothing more. It is *not* the abstraction
`ownRaftPhys` is indexed by -- that is the physical abstract state `NState`
(`Defs.lean`), which carries whatever the Go-level specs need (the `r.step` function,
the progress map, the log's abstract state) on top of these fields. The two are
connected by `NStateRel` (`Defs.lean`); `Step`'s spec is the one place that crosses
from one to the other. See main's notes/decisions.md, "Three layers".

`outbox` is the node's pending outgoing messages — the abstraction of the Go code's
two queues, `r.msgs` and `r.msgsAfterAppend`, together. Keeping it in the state
rather than as a separate output of `Step` is what lets "this function sent a
message" be just "the outbox grew". -/

structure PState where
  /-- `raft.Term` -/
  term : w64
  /-- `raft.Vote`; `W64 0` is the Go code's `None` -/
  vote : w64
  /-- `raft.lead`; `W64 0` is the Go code's `None` -/
  lead : w64
  /-- `raft.state` -/
  role : Role
  /-- `raft.trk.Votes` -/
  votes : GMap w64 Bool
  /-- `r.msgs` and `r.msgsAfterAppend`, together -/
  outbox : List Msg

section model

-- `cfg` is the (fixed) set of voters; `id` the node being described.
variable (cfg : GSet w64) (id : w64)

def IsQuorum (q : GSet w64) : Prop := size cfg < 2 * size (q ∩ cfg)

/-- Two quorums meet. This is the whole content of election safety. -/
theorem quorums_intersect (q1 q2 : GSet w64) :
    IsQuorum cfg q1 → IsQuorum cfg q2 → ∃ x, x ∈ q1 ∧ x ∈ q2 := by
  intro Hsize1 Hsize2
  by_cases Hempty : q1 ∩ q2 = ∅
  · exfalso
    have Hunion : (q1 ∩ cfg) ∪ (q2 ∩ cfg) ⊆ cfg := by
      rw [GMap.elem_of_subseteq]; set_solver
    have Hdisj : (q1 ∩ cfg) ## (q2 ∩ cfg) := by
      rw [GMap.elem_of_disjoint]
      intro x h1 h2
      rw [GMap.elem_of_intersection] at h1 h2
      have : x ∈ q1 ∩ q2 := (GMap.elem_of_intersection _ _ _).mpr ⟨h1.1, h2.1⟩
      rw [Hempty] at this
      exact GMap.not_elem_of_empty _ this
    have Hle := GMap.subseteq_size Hunion
    rw [GMap.size_union Hdisj] at Hle
    unfold IsQuorum at *
    omega
  · obtain ⟨x, Hx⟩ := GMap.set_choose_L _ Hempty
    exact ⟨x, by set_solver, by set_solver⟩

def granted (votes : GMap w64 Bool) : GSet w64 :=
  domSet (filter (fun _ v => v) votes)

def rejected (votes : GMap w64 Bool) : GSet w64 :=
  domSet (filter (fun _ v => !v) votes)

/-- Putting messages on the network. -/
def psendMsgs (s : PState) (ms : List Msg) : PState :=
  { s with outbox := s.outbox ++ ms }

/-! ### Role transitions

These mirror the Go code exactly. `reset(term)` clears `Vote` only when the term
actually changes, always clears `lead` and the vote tally; the `becomeX` wrappers
then set `lead` and `state`. None of them sends, so all three carry the outbox across
unchanged. -/

def pbecomeFollower (s : PState) (term lead : w64) : PState where
  term := term
  vote := if term = s.term then s.vote else W64 0
  lead := lead
  role := .follower
  votes := ∅
  outbox := s.outbox

def pbecomeCandidate (s : PState) : PState where
  term := s.term + W64 1
  vote := id
  lead := W64 0
  role := .candidate
  votes := ∅
  outbox := s.outbox

def pbecomeLeader (s : PState) : PState where
  term := s.term
  vote := s.vote
  lead := id
  role := .leader
  votes := ∅
  outbox := s.outbox

/-- `raft.trk.RecordVote`: the first vote recorded for a node wins; later ones are
dropped. -/
def recordVote (votes : GMap w64 Bool) (src : w64) (v : Bool) : GMap w64 Bool :=
  match votes !! src with
  | some _ => votes
  | none => <[src := v]> votes

/-- A node may grant its vote to `src` in its current term when it has not already
voted for somebody else and does not currently recognise a leader. (The Go code
additionally requires the candidate's log to be up to date, which can only turn a
grant into a rejection; rejecting is always legal, so that check is invisible here.) -/
def PCanVote (s : PState) (src : w64) : Prop :=
  s.vote = src ∨ (s.vote = W64 0 ∧ s.lead = W64 0)

/-! ### The transition relation

`Step s recv s'` says: a node in state `s`, making use of the already-sent messages
`recv`, may move to state `s'`. Messages the node itself sends are not a separate
output: they are the growth of `s'.outbox`.

Reflexivity and transitivity are part of the relation so that a single Go function
which performs several protocol steps (e.g. `campaign`, which becomes a candidate
*and* broadcasts vote requests, or a `MsgVoteResp` that both records a vote and wins
the election) refines a single `Step`. -/

inductive Step : PState → List Msg → PState → Prop where
  /-- structural rules -/
  | refl (s : PState) : Step s [] s
  | trans (s₀ : PState) (r₁ : List Msg) (s₁ : PState) (r₂ : List Msg) (s₂ : PState) :
      Step s₀ r₁ s₁ → Step s₁ r₂ s₂ → Step s₀ (r₁ ++ r₂) s₂
  /-- `Step`'s term preamble: a message from a higher term makes the node step down.
  It adopts the sender as leader exactly when the message is one only a leader
  sends. -/
  | higherTerm (m : Msg) (s : PState) :
      uint.Z s.term < uint.Z m.term →
      m.dst = id →
      Step s [m] (pbecomeFollower s m.term (if fromLeader m.ty then m.src else W64 0))
  /-- `hup` / `campaign`: a non-leader starts an election. It increments its term,
  votes for itself, and sends a `MsgVote` to every other voter plus a self-addressed
  `MsgVoteResp` (which the Go code routes through `msgsAfterAppend`).

  The term increments, and a term that wrapped round to one the node has already
  voted in would let it vote twice in that term -- which is exactly what election
  safety rests on not happening. `Step`'s spec already carries this for a `MsgHup`,
  because `send` panics on a zero term; here is where it is needed. -/
  | campaign (s : PState) (peers : List w64) :
      s.role ≠ .leader →
      id ∈ cfg →
      uint.Z s.term + 1 < 2 ^ 64 →
      peers ≡ₚ elements (cfg \ {[id]}) →
      Step s []
        (psendMsgs (pbecomeCandidate id s)
          ([⟨.voteResp, id, id, (pbecomeCandidate id s).term, false⟩] ++
           peers.map (fun dst => ⟨.vote, id, dst, (pbecomeCandidate id s).term, false⟩)))
  /-- Granting a vote.

  `W64 0` is the Go code's `None`, so a vote *for* it is not a vote at all:
  `vote = W64 0` is how "has not voted this term" is written. Without the `src ≠ 0`
  premise, granting to `W64 0` and then granting again would be two votes in one
  term. `Step`'s spec already requires it of a `MsgVote`. -/
  | grantVote (m : Msg) (s : PState) :
      m.ty = .vote →
      m.dst = id →
      m.src ≠ W64 0 →
      m.term = s.term →
      PCanVote s m.src →
      Step s [m] (psendMsgs { s with vote := m.src } [⟨.voteResp, id, m.src, s.term, false⟩])
  /-- Refusing a vote. Always legal, so the Go code's extra conditions (`isUpToDate`,
  and the `m.Term < r.Term` case which drops the message silently) are covered by
  this rule and by `refl`. -/
  | rejectVote (m : Msg) (s : PState) :
      m.ty = .vote →
      m.dst = id →
      Step s [m] (psendMsgs s [⟨.voteResp, id, m.src, s.term, true⟩])
  /-- `stepCandidate` / `poll`: record a vote response for the current term. -/
  | recordVote (m : Msg) (s : PState) :
      m.ty = .voteResp →
      m.dst = id →
      m.term = s.term →
      s.role = .candidate →
      Step s [m] { s with votes := recordVote s.votes m.src (!m.reject) }
  /-- Winning: a quorum of grants makes the candidate leader, and it immediately
  broadcasts appends.

  The sends are deliberately loose: **any** list of `App` messages from `id` at the
  current term, including none at all. An earlier version required exactly one per
  peer, and that is **not what the code does**: `bcastAppend` reaches
  `maybeSendAppend`, which sends a `MsgApp` only when the log and the peer's
  `Progress` allow it, and otherwise sends a `MsgSnap` or nothing. Pinning the exact
  broadcast down would need the log and `Progress.State` to be non-opaque, which is
  log replication rather than election.

  Nothing is lost: election safety follows from quorum intersection on `votes`, and
  no rule reads an `App`'s payload. A receiver only ever uses an `App` through
  `higherTerm`, which cares about its term and that a leader sent it — both of which
  are still pinned here. -/
  | win (s : PState) (ms : List Msg) :
      s.role = .candidate →
      IsQuorum cfg (granted s.votes) →
      (∀ m ∈ ms, m.ty = .app ∧ m.src = id ∧ m.term = s.term) →
      Step s [] (psendMsgs (pbecomeLeader id s) ms)
  /-- Losing: the candidate cannot win any more, so it goes back to follower in the
  same term.

  Go's `MajorityConfig.VoteResult` returns `VoteLost` when `votedCnt + missing < q`,
  i.e. when the candidate **cannot still win** -- not when a majority has rejected
  it. The two differ, and the earlier premise `IsQuorum (rejected votes)` was
  therefore **false of the code**: with 4 voters, 2 rejecting and 2 yet to vote, the
  count is `0 + 2 < 3` so Go says `VoteLost`, while the 2 rejections are not a quorum.

  Working the identity through: `votedCnt + missing = size cfg - size (rejected ∩
  cfg) = size (cfg \ rejected)`, so `VoteLost ⇔ ¬ IsQuorum (cfg \ rejected)` -- the
  voters who have *not* rejected are not a quorum. That is what this premise says.

  Weakening it is safe: `lose` moves a candidate to follower at the same term and
  creates no leader, so election safety is untouched. -/
  | lose (s : PState) :
      s.role = .candidate →
      ¬ IsQuorum cfg (cfg \ rejected s.votes) →
      Step s [] (pbecomeFollower s s.term (W64 0))
  /-- `Ready` hands the pending messages to the transport, emptying the queues.
  Dropping messages from one's own outbox is always legal: the `IsMessage` facts
  handed out for them are persistent and survive. `Ready` is out of scope for the
  election proof, but without this rule the model's outbox could only ever grow,
  which the physical state could not refine past the first drain. -/
  | drain (s : PState) (o' : List Msg) :
      o'.Subperm s.outbox →
      Step s [] { s with outbox := o' }

end model

/-- A set as the map it is (`GSet K = GMap K Unit`), for `[∗map] k ↦ _ ∈ toMap X, …`, the
`[∗ set]` of Rocq. -/
@[reducible] def toMap {K : Type} (X : GSet K) : GMap K Unit := X

/-! ## Ghost state

The ghost state is deliberately *node-local*: there is no Iris invariant here and
nothing global to open. Each node owns the authority over its own vote history —
which candidate it voted for in each term — and that authority is the exclusive part
of `ownRaftGhost`. Everything a step needs to *learn* is persistent knowledge, so it
can ride on a message or be held across a step with nowhere to put it.

Three pieces:
* `isVote γ v term cand` — node `v` voted for `cand` in `term`. Frozen into `v`'s map
  when it is allocated, so it is persistent, and unforgeable because allocating it
  takes `v`'s own authority.
* `isMessage γ m` — what a legitimately sent message carries. Only a *granting*
  `voteResp` carries anything: the vote it reports.
* `isLeader γ id term` — a quorum of `isVote`s for `id` at `term`.

Election safety is then quorum intersection plus the agreement of two `isVote`s for
one node and term; that is all `isLeader_unique` is.

What holds a node to one vote per term is `VoteHistOk`, the pure invariant inside
`ownRaftGhost` tying the history to the current `(term, vote)`: the history mentions
only terms the node has reached, and at the current term it agrees with `vote` —
where `W64 0`, the Go code's `None`, means the term is absent from the history
altogether. Every rule that clears `vote` raises `term` past everything in the
history, which is exactly why `Step.campaign` needs its no-wrap premise and
`Step.grantVote` its `src ≠ 0`. -/

structure RaftElectionNames where
  /-- The voter set this ghost state is about. It lives in `γ` rather than being a
  parameter of `ownRaftGhost_step`: a step free to choose its own `cfg` could choose a
  singleton one and elect itself, and the quorum `Step.win` demands has to be a quorum
  of the same configuration `isLeader_unique` intersects in. -/
  reCfg : GSet w64
  /-- `reVotes !! id` names the ghost map holding node `id`'s vote history,
  `term ↦ candidate`. A node absent from here has no ghost state at all. -/
  reVotes : GMap w64 GName

section ghost

variable {GF : BundledGFunctors} [AllG GF]

/-! ### Votes -/

def isVote (γ : RaftElectionNames) (v term cand : w64) : IProp GF :=
  iprop(∃ γv, ⌜γ.reVotes !! v = some γv⌝ ∗ term ↪[γv]□ cand)

instance isVote_persistent (γ : RaftElectionNames) (v term cand : w64) :
    Persistent (isVote (GF := GF) γ v term cand) := by
  unfold isVote; infer_instance

instance isVote_timeless (γ : RaftElectionNames) (v term cand : w64) :
    Timeless (isVote (GF := GF) γ v term cand) := by
  unfold isVote; infer_instance

/-- One vote per node per term. This is the other half of election safety. -/
theorem isVote_agree (γ : RaftElectionNames) (v term c1 c2 : w64) :
    ⊢ isVote (GF := GF) γ v term c1 -∗ isVote γ v term c2 -∗ ⌜c1 = c2⌝ := by
  unfold isVote
  iintro ⟨%γ1, %Hγ1, H1⟩ ⟨%γ2, %Hγ2, H2⟩
  rw [Hγ1] at Hγ2
  cases Hγ2
  iapply ghostMapElem_agree $$ H1 H2

/-! ### Messages -/

def isMessage (γ : RaftElectionNames) (m : Msg) : IProp GF :=
  match m.ty with
  | .voteResp => if m.reject then iprop(True) else isVote γ m.src m.term m.dst
  | _ => iprop(True)

instance isMessage_persistent (γ : RaftElectionNames) (m : Msg) :
    Persistent (isMessage (GF := GF) γ m) := by
  unfold isMessage; split <;> (try split) <;> infer_instance

instance isMessage_timeless (γ : RaftElectionNames) (m : Msg) :
    Timeless (isMessage (GF := GF) γ m) := by
  unfold isMessage; split <;> (try split) <;> infer_instance

/-- Every message but a granting `voteResp` is free. -/
theorem isMessage_triv (γ : RaftElectionNames) (m : Msg) (Hty : m.ty ≠ .voteResp) :
    ⊢ isMessage (GF := GF) γ m := by
  unfold isMessage
  cases h : m.ty <;> simp only [h] at Hty ⊢ <;> first | exact absurd rfl Hty | exact true_intro

/-- A list of messages none of which is a `voteResp` is free. -/
theorem isMessage_triv_list (γ : RaftElectionNames) (l : List Msg)
    (H : ∀ m ∈ l, m.ty ≠ .voteResp) :
    ⊢ [∗list] m ∈ l, isMessage (GF := GF) γ m := by
  induction l with
  | nil => exact (BigSepL.bigSepL_nil (Φ := fun _ m => isMessage (GF := GF) γ m)).2
  | cons x xs ih =>
    iapply (BigSepL.bigSepL_cons (Φ := fun _ m => isMessage (GF := GF) γ m)).2
    isplitl
    · iapply isMessage_triv γ x (H x (by simp))
    · iapply ih (fun m hm => H m (by simp [hm]))

/-- A *rejecting* `voteResp` is free too: it reports no vote. -/
theorem isMessage_reject (γ : RaftElectionNames) (src dst term : w64) :
    ⊢ isMessage (GF := GF) γ ⟨.voteResp, src, dst, term, true⟩ := by
  unfold isMessage; exact true_intro

/-- A granting `voteResp` carries the vote it reports, and nothing else. -/
theorem isMessage_grant (γ : RaftElectionNames) (src dst term : w64) :
    isVote (GF := GF) γ src term dst ⊢ isMessage γ ⟨.voteResp, src, dst, term, false⟩ := by
  unfold isMessage; exact .rfl

theorem isMessage_grant_inv (γ : RaftElectionNames) (m : Msg)
    (Hty : m.ty = .voteResp) (Hrej : m.reject = false) :
    isMessage (GF := GF) γ m ⊢ isVote γ m.src m.term m.dst := by
  unfold isMessage; rw [Hty]; simp only [Hrej]; exact .rfl

/-! ### Leadership -/

def isLeader (γ : RaftElectionNames) (id term : w64) : IProp GF :=
  iprop(∃ q, ⌜IsQuorum γ.reCfg q⌝ ∗ [∗map] v ↦ _u ∈ (toMap q), isVote γ v term id)

instance isLeader_persistent (γ : RaftElectionNames) (id term : w64) :
    Persistent (isLeader (GF := GF) γ id term) := by
  unfold isLeader; infer_instance

instance isLeader_timeless (γ : RaftElectionNames) (id term : w64) :
    Timeless (isLeader (GF := GF) γ id term) := by
  unfold isLeader; infer_instance

/-! ## Election safety

Two leaders in one term were each elected by a quorum; the quorums meet in a voter
that cast one vote. -/
theorem isLeader_unique (γ : RaftElectionNames) (id1 id2 term : w64) :
    ⊢ isLeader (GF := GF) γ id1 term -∗ isLeader γ id2 term -∗ ⌜id1 = id2⌝ := by
  unfold isLeader
  iintro ⟨%q1, %Hq1, #H1⟩ ⟨%q2, %Hq2, #H2⟩
  obtain ⟨v, Hv1, Hv2⟩ := quorums_intersect _ _ _ Hq1 Hq2
  ihave #Hv1 := BigSepM.bigSepM_lookup (Φ := fun v _ => isVote (GF := GF) γ v term id1) ((GMap.elem_of_gset _ _).mp Hv1) $$ H1
  ihave #Hv2 := BigSepM.bigSepM_lookup (Φ := fun v _ => isVote (GF := GF) γ v term id2) ((GMap.elem_of_gset _ _).mp Hv2) $$ H2
  iapply isVote_agree $$ Hv1 Hv2

/-! ### A node's protocol state -/

def VoteHistOk (voted : GMap w64 w64) (s : PState) : Prop :=
  (∀ t, (voted !! t).isSome → uint.Z t ≤ uint.Z s.term) ∧
  voted !! s.term = (if s.vote = W64 0 then none else some s.vote)

/-- A term the node has not reached yet is free to vote in. -/
theorem voteHist_fresh (voted : GMap w64 w64) (s : PState) (t : w64)
    (H : VoteHistOk voted s) (Hlt : uint.Z s.term < uint.Z t) : voted !! t = none := by
  cases h : voted !! t with
  | none => rfl
  | some c =>
    have := H.1 t (by simp [h])
    omega

/-- `VoteHistOk` reads only `term` and `vote`, so every rule that touches the outbox,
the tally or the role preserves it. -/
theorem voteHistOk_eq (voted : GMap w64 w64) (s1 s2 : PState) (H : VoteHistOk voted s1)
    (Ht : s2.term = s1.term) (Hv : s2.vote = s1.vote) : VoteHistOk voted s2 := by
  unfold VoteHistOk at *; rw [Ht, Hv]; exact H

def leaderWit (γ : RaftElectionNames) (id : w64) (s : PState) : IProp GF :=
  match s.role with
  | .leader => isLeader γ id s.term
  | _ => iprop(True)

instance leaderWit_persistent (γ : RaftElectionNames) (id : w64) (s : PState) :
    Persistent (leaderWit (GF := GF) γ id s) := by
  unfold leaderWit; cases s.role <;> simp only <;> infer_instance

instance leaderWit_timeless (γ : RaftElectionNames) (id : w64) (s : PState) :
    Timeless (leaderWit (GF := GF) γ id s) := by
  unfold leaderWit; cases s.role <;> simp only <;> infer_instance

def ownRaftGhost (γ : RaftElectionNames) (id : w64) (s : PState) : IProp GF :=
  iprop(∃ γv voted,
    "%Hname" ∷ ⌜γ.reVotes !! id = some γv⌝ ∗
    "%Hidnz" ∷ ⌜id ≠ W64 0⌝ ∗
    "Hvoted" ∷ ghostMapAuth γv 1 voted ∗
    "%Hhist" ∷ ⌜VoteHistOk voted s⌝ ∗
    "#Hfrags" ∷ ([∗map] t ↦ c ∈ voted, isVote γ id t c) ∗
    "#Hout" ∷ ([∗list] m ∈ s.outbox, isMessage γ m) ∗
    "#Htally" ∷ ([∗map] v ↦ _u ∈ (toMap (granted s.votes)), isVote γ v s.term id) ∗
    "#Hlead" ∷ leaderWit γ id s)

instance ownRaftGhost_timeless (γ : RaftElectionNames) (id : w64) (s : PState) :
    Timeless (ownRaftGhost (GF := GF) γ id s) := by
  unfold ownRaftGhost; infer_instance

theorem ownRaftGhost_intro (γ : RaftElectionNames) (id : w64) (s : PState) (γv : GName)
    (voted : GMap w64 w64) (Hname : γ.reVotes !! id = some γv) (Hidnz : id ≠ W64 0) :
    ⊢ ghostMapAuth (GF := GF) γv 1 voted -∗ ⌜VoteHistOk voted s⌝ -∗
      ([∗map] t ↦ c ∈ voted, isVote γ id t c) -∗
      ([∗list] m ∈ s.outbox, isMessage γ m) -∗
      ([∗map] v ↦ _u ∈ (toMap (granted s.votes)), isVote γ v s.term id) -∗
      leaderWit γ id s -∗
      ownRaftGhost γ id s := by
  unfold ownRaftGhost
  iintro H1 %H2 #H3 #H4 #H5 #H6
  iexists γv, voted
  isplitr; · ipureintro; exact Hname
  isplitr; · ipureintro; exact Hidnz
  isplitl [H1]; · iexact H1
  isplitr; · ipureintro; exact H2
  iframe # ∗

theorem ownRaftGhost_excl (γ : RaftElectionNames) (id : w64) (s1 s2 : PState) :
    ⊢ ownRaftGhost (GF := GF) γ id s1 -∗ ownRaftGhost γ id s2 -∗ False := by
  unfold ownRaftGhost
  iintro ⟨%γ1, %v1, %Hn1, -, H1, -⟩ ⟨%γ2, %v2, %Hn2, -, H2, -⟩
  rw [Hn1] at Hn2
  cases Hn2
  icases ghostMapAuth_valid_2 $$ H1 H2 with %⟨Hq, -⟩
  exfalso
  have : (1 : Rat) + 1 ≤ 1 := Hq
  grind

/-- Everything in a node's outbox was legitimately put there. This is a plain
entailment, not an update: `ownRaftGhost` carries the `isMessage`s directly rather
than deriving them from an invariant. -/
theorem ownRaftGhost_outbox (γ : RaftElectionNames) (id : w64) (s : PState) :
    ownRaftGhost (GF := GF) γ id s ⊢ [∗list] m ∈ s.outbox, isMessage γ m := by
  unfold ownRaftGhost
  iintro ⟨%_, %_, -, -, -, -, -, #H, -⟩
  iexact H

theorem ownRaftGhost_isLeader (γ : RaftElectionNames) (id : w64) (s : PState)
    (Hrole : s.role = .leader) :
    ownRaftGhost (GF := GF) γ id s ⊢ isLeader γ id s.term := by
  unfold ownRaftGhost
  iintro ⟨%_, %_, -, -, -, -, -, -, -, #H⟩
  unfold leaderWit; rw [Hrole]
  iexact H

/-! ### Pure facts about the vote tally

`granted` is a `domSet` of a `filter`; these three are the only shapes the step
proof needs. -/

theorem elem_of_granted (votes : GMap w64 Bool) (v : w64) :
    v ∈ granted votes ↔ votes !! v = some true := by
  unfold granted
  rw [GMap.elem_of_dom]
  constructor
  · rintro ⟨b, Hb⟩
    rw [GMap.mapLookup_filter_Some] at Hb
    obtain ⟨Hv, Hb⟩ := Hb
    cases b
    · exact absurd Hb (by decide)
    · exact Hv
  · intro Hv
    exact ⟨true, (GMap.mapLookup_filter_Some _ _ _ _).mpr ⟨Hv, rfl⟩⟩

theorem granted_empty : granted ∅ = ∅ := by
  unfold granted; rw [GMap.map_filter_empty, GMap.dom_empty_L]

theorem elem_of_granted_recordVote (votes : GMap w64 Bool) (src : w64) (b : Bool) (v : w64)
    (H : v ∈ granted (recordVote votes src b)) :
    v ∈ granted votes ∨ (v = src ∧ b = true) := by
  unfold recordVote at H
  cases Hf : votes !! src with
  | some _ => simp only [Hf] at H; exact .inl H
  | none =>
    simp only [Hf] at H
    rw [elem_of_granted] at H ⊢
    by_cases Hv : v = src
    · subst Hv; rw [GMap.lookup_insert_eq] at H; cases H; exact .inr ⟨rfl, rfl⟩
    · rw [GMap.lookup_insert_ne _ _ (Ne.symm Hv)] at H; exact .inl H

end ghost

/-! ### The refinement obligation -/

section step

variable {GF : BundledGFunctors} [InvGS GF] [AllG GF]

/-- `[∗list]` is monotone along `List.Subperm`. -/
theorem bigSepL_subperm {A : Type _} (Φ : A → IProp GF) {l₁ l₂ : List A}
    (h : l₁.Subperm l₂) : ([∗list] x ∈ l₂, Φ x) ⊢ [∗list] x ∈ l₁, Φ x := by
  obtain ⟨l, hperm, hsub⟩ := h
  obtain ⟨rest, hrest⟩ := hsub.exists_perm_append
  have h1 : ([∗list] x ∈ l₂, Φ x) ⊢ [∗list] x ∈ l, Φ x := BigSepL.bigSepL_submseteq hrest.symm
  have h2 : ([∗list] x ∈ l, Φ x) ⊢ [∗list] x ∈ l₁, Φ x := (BigSepL.bigSepL_perm hperm).1
  exact h1.trans h2

theorem gset_lookup_none {X : GSet w64} {v : w64} (H : v ∉ X) : X !! v = none := by
  cases h : X !! v with
  | none => rfl
  | some u => exact absurd ((GMap.elem_of_gset _ _).mpr h) H

theorem not_mem_granted_of_none (votes : GMap w64 Bool) (v : w64) (H : votes !! v = none) :
    v ∉ granted votes := by
  rw [elem_of_granted, H]; simp

/-- A fresh grant adds its voter to the tally. -/
theorem granted_insert_true (votes : GMap w64 Bool) (v : w64) (_H : votes !! v = none) :
    granted (<[v := true]> votes) = <[v := ()]> (granted votes) := by
  apply GMap.set_eq; intro x
  rw [elem_of_granted, GMap.elem_of_gset]
  by_cases Hx : x = v
  · subst Hx; simp [GMap.lookup_insert_eq]
  · rw [GMap.lookup_insert_ne _ _ (Ne.symm Hx), GMap.lookup_insert_ne _ _ (Ne.symm Hx),
      ← GMap.elem_of_gset, elem_of_granted]

/-- A fresh rejection does not change the tally. -/
theorem granted_insert_false (votes : GMap w64 Bool) (v : w64) (H : votes !! v = none) :
    granted (<[v := false]> votes) = granted votes := by
  apply GMap.set_eq; intro x
  rw [elem_of_granted, elem_of_granted]
  by_cases Hx : x = v
  · subst Hx; simp [GMap.lookup_insert_eq, H]
  · rw [GMap.lookup_insert_ne _ _ (Ne.symm Hx)]

/-- `pbecomeFollower` keeps the vote only when the term does not move. -/
theorem pbecomeFollower_vote_ne (s : PState) (term lead : w64) (Hne : term ≠ s.term) :
    (pbecomeFollower s term lead).vote = W64 0 := by
  simp [pbecomeFollower, Hne]

theorem pbecomeFollower_vote_same (s : PState) (lead : w64) :
    (pbecomeFollower s s.term lead).vote = s.vote := by
  simp [pbecomeFollower]

theorem ownRaftGhost_step (γ : RaftElectionNames) (id : w64) (s : PState) (recv : List Msg)
    (s' : PState) (Hstep : Step γ.reCfg id s recv s') :
    ⊢ ([∗list] m ∈ recv, isMessage (GF := GF) γ m) -∗ ownRaftGhost γ id s ={⊤}=∗
      ownRaftGhost γ id s' := by
  induction Hstep with
  | refl s =>
    iintro _ Hown
    imodintro; iexact Hown
  | trans s0 r1 s1 r2 s2 _ _ IH1 IH2 =>
    iintro Hrecv Hown
    icases (BigSepL.bigSepL_append (Φ := fun _ m => isMessage (GF := GF) γ m)).1 $$ Hrecv
      with ⟨Hr1, Hr2⟩
    imod IH1 $$ Hr1 Hown with Hown
    iapply IH2 $$ Hr2 Hown
  | higherTerm m s Hlt Hto =>
    -- a strictly greater term, so the vote is cleared and the new term is fresh in
    -- the history
    iintro _ Hown
    unfold ownRaftGhost
    icases Hown with ⟨%γv, %voted, Hown⟩
    iNamed Hown
    have Hne : m.term ≠ s.term := by intro Heq; rw [Heq] at Hlt; omega
    have Hhist' : VoteHistOk voted
        (pbecomeFollower s m.term (if fromLeader m.ty then m.src else W64 0)) := by
      unfold VoteHistOk
      rw [pbecomeFollower_vote_ne _ _ _ Hne]
      refine ⟨fun t Ht => ?_, ?_⟩
      · have := Hhist.1 t Ht; simp only [pbecomeFollower]; omega
      · simp only [pbecomeFollower, ↓reduceIte]
        exact voteHist_fresh voted s _ Hhist Hlt
    imodintro
    iexists γv, voted
    iframe Hvoted Hfrags
    isplitr; · ipureintro; exact Hname
    isplitr; · ipureintro; exact Hidnz
    isplitr; · ipureintro; exact Hhist'
    isplitr; · simp only [pbecomeFollower]; iexact Hout
    isplitr
    · simp only [pbecomeFollower, granted_empty]
      iapply BigSepM.bigSepM_empty.2; iempintro
    · unfold leaderWit; simp only [pbecomeFollower]; iempintro
  | campaign s peers Hrole Hin Hnowrap Hperm =>
    -- the term goes up by one, so it is fresh, and the node votes for itself there
    iintro _ Hown
    unfold ownRaftGhost
    icases Hown with ⟨%γv, %voted, Hown⟩
    iNamed Hown
    have Ht' : uint.Z (s.term + W64 1) = uint.Z s.term + 1 := by word
    have Hfree : voted !! (s.term + W64 1) = none :=
      voteHist_fresh voted s _ Hhist (by omega)
    imod ghost_map_insert_persist (s.term + W64 1) id Hfree $$ Hvoted with ⟨Hvoted, #Hself⟩
    ihave #Hisvote : isVote (GF := GF) γ id (s.term + W64 1) id $$ []
    · unfold isVote; iexists γv; iframe Hself; ipureintro; exact Hname
    have Hhist' : VoteHistOk (<[s.term + W64 1 := id]> voted) (pbecomeCandidate id s) := by
      unfold VoteHistOk pbecomeCandidate
      refine ⟨fun t Ht => ?_, ?_⟩
      · by_cases Htt : t = s.term + W64 1
        · subst Htt; simp only; omega
        · rw [GMap.lookup_insert_ne _ _ (Ne.symm Htt)] at Ht
          have := Hhist.1 t Ht; simp only; omega
      · simp only [GMap.lookup_insert_eq, if_neg Hidnz]
    imodintro
    iexists γv, (<[s.term + W64 1 := id]> voted)
    iframe Hvoted
    isplitr; · ipureintro; exact Hname
    isplitr; · ipureintro; exact Hidnz
    isplitr; · ipureintro; exact Hhist'
    isplitr
    · iapply (BigSepM.bigSepM_insert (Φ := fun t c => isVote (GF := GF) γ id t c) Hfree).2
      iframe # ∗
    isplitr
    · unfold psendMsgs pbecomeCandidate
      simp only
      iapply (BigSepL.bigSepL_append (Φ := fun _ m => isMessage (GF := GF) γ m)).2
      isplitr; · iexact Hout
      iapply (BigSepL.bigSepL_append (Φ := fun _ m => isMessage (GF := GF) γ m)).2
      isplitr
      · iapply (BigSepL.bigSepL_singleton (Φ := fun _ m => isMessage (GF := GF) γ m)).2
        iapply isMessage_grant $$ Hisvote
      · iapply isMessage_triv_list
        intro x hx
        obtain ⟨dst, -, rfl⟩ := List.mem_map.mp hx
        simp
    isplitr
    · simp only [psendMsgs, pbecomeCandidate, granted_empty]
      iapply BigSepM.bigSepM_empty.2; iempintro
    · unfold leaderWit; simp only [psendMsgs, pbecomeCandidate]; iempintro
  | grantVote m s Hty Hto Hsrc Hterm Hcan =>
    -- either the node has already voted this way, or the current term is free in the
    -- history
    iintro _ Hown
    unfold ownRaftGhost
    icases Hown with ⟨%γv, %voted, Hown⟩
    iNamed Hown
    have Hhist' : ∀ voted', VoteHistOk voted' { s with vote := m.src } →
        VoteHistOk voted' (psendMsgs { s with vote := m.src }
          [⟨.voteResp, id, m.src, s.term, false⟩]) :=
      fun _ H => voteHistOk_eq _ _ _ H rfl rfl
    rcases Hcan with Hsame | ⟨Hnovote, _⟩
    · -- already voted for this candidate
      have Hvnz : s.vote ≠ W64 0 := by rw [Hsame]; exact Hsrc
      have Hlook : voted !! s.term = some m.src := by rw [Hhist.2, if_neg Hvnz, Hsame]
      ihave #Hgrant := BigSepM.bigSepM_lookup (Φ := fun t c => isVote (GF := GF) γ id t c)
        Hlook $$ Hfrags
      imodintro
      iexists γv, voted
      iframe Hvoted Hfrags
      isplitr; · ipureintro; exact Hname
      isplitr; · ipureintro; exact Hidnz
      isplitr
      · ipureintro
        exact Hhist' voted ⟨Hhist.1, by simp only; rw [Hhist.2, if_neg Hvnz, if_neg Hsrc, Hsame]⟩
      isplitr
      · simp only [psendMsgs]
        iapply (BigSepL.bigSepL_append (Φ := fun _ m => isMessage (GF := GF) γ m)).2
        isplitr; · iexact Hout
        iapply (BigSepL.bigSepL_singleton (Φ := fun _ m => isMessage (GF := GF) γ m)).2
        iapply isMessage_grant $$ Hgrant
      isplitr; · simp only [psendMsgs]; iexact Htally
      · unfold leaderWit; simp only [psendMsgs]; iexact Hlead
    · -- first vote of this term
      have Hfree : voted !! s.term = none := by rw [Hhist.2, if_pos Hnovote]
      imod ghost_map_insert_persist s.term m.src Hfree $$ Hvoted with ⟨Hvoted, #Hnew⟩
      ihave #Hgrant : isVote (GF := GF) γ id s.term m.src $$ []
      · unfold isVote; iexists γv; iframe Hnew; ipureintro; exact Hname
      imodintro
      iexists γv, (<[s.term := m.src]> voted)
      iframe Hvoted
      isplitr; · ipureintro; exact Hname
      isplitr; · ipureintro; exact Hidnz
      isplitr
      · ipureintro
        refine Hhist' _ ⟨fun t Ht => ?_, ?_⟩
        · by_cases Htt : t = s.term
          · subst Htt; simp only; omega
          · rw [GMap.lookup_insert_ne _ _ (Ne.symm Htt)] at Ht
            exact Hhist.1 t Ht
        · simp only [GMap.lookup_insert_eq, if_neg Hsrc]
      isplitr
      · iapply (BigSepM.bigSepM_insert (Φ := fun t c => isVote (GF := GF) γ id t c) Hfree).2
        iframe # ∗
      isplitr
      · simp only [psendMsgs]
        iapply (BigSepL.bigSepL_append (Φ := fun _ m => isMessage (GF := GF) γ m)).2
        isplitr; · iexact Hout
        iapply (BigSepL.bigSepL_singleton (Φ := fun _ m => isMessage (GF := GF) γ m)).2
        iapply isMessage_grant $$ Hgrant
      isplitr; · simp only [psendMsgs]; iexact Htally
      · unfold leaderWit; simp only [psendMsgs]; iexact Hlead
  | rejectVote m s Hty Hto =>
    -- a rejection carries nothing
    iintro _ Hown
    unfold ownRaftGhost
    icases Hown with ⟨%γv, %voted, Hown⟩
    iNamed Hown
    imodintro
    iexists γv, voted
    iframe Hvoted Hfrags
    isplitr; · ipureintro; exact Hname
    isplitr; · ipureintro; exact Hidnz
    isplitr; · ipureintro; exact voteHistOk_eq _ _ _ Hhist rfl rfl
    isplitr
    · simp only [psendMsgs]
      iapply (BigSepL.bigSepL_append (Φ := fun _ m => isMessage (GF := GF) γ m)).2
      isplitr; · iexact Hout
      iapply (BigSepL.bigSepL_singleton (Φ := fun _ m => isMessage (GF := GF) γ m)).2
      iapply isMessage_reject
    isplitr; · simp only [psendMsgs]; iexact Htally
    · unfold leaderWit; simp only [psendMsgs]; iexact Hlead
  | recordVote m s Hty Hto Hterm Hrole =>
    -- a granting response is backed by the voter's vote
    iintro Hrecv Hown
    icases (BigSepL.bigSepL_cons (Φ := fun _ m => isMessage (GF := GF) γ m)).1 $$ Hrecv
      with ⟨#Hm, -⟩
    unfold ownRaftGhost
    icases Hown with ⟨%γv, %voted, Hown⟩
    iNamed Hown
    imodintro
    iexists γv, voted
    iframe Hvoted Hfrags
    isplitr; · ipureintro; exact Hname
    isplitr; · ipureintro; exact Hidnz
    isplitr; · ipureintro; exact voteHistOk_eq _ _ _ Hhist rfl rfl
    isplitr; · iexact Hout
    isplitr
    · simp only
      unfold recordVote
      cases Hf : s.votes !! m.src with
      | some _ => simp only; iexact Htally
      | none =>
        simp only
        cases Hrej : m.reject with
        | true =>
          simp only [Bool.not_true]
          rw [granted_insert_false _ _ Hf]
          iexact Htally
        | false =>
          simp only [Bool.not_false]
          rw [granted_insert_true _ _ Hf]
          iapply (BigSepM.bigSepM_insert (Φ := fun v _ => isVote (GF := GF) γ v s.term id)
            (gset_lookup_none (not_mem_granted_of_none _ _ Hf))).2
          isplitr
          · rw [← Hterm, ← Hto]
            iapply isMessage_grant_inv γ m Hty Hrej $$ Hm
          · iexact Htally
    · unfold leaderWit; simp only; iexact Hlead
  | win s ms Hrole Hq Hms =>
    -- the tally is the quorum that elected the node
    iintro _ Hown
    unfold ownRaftGhost
    icases Hown with ⟨%γv, %voted, Hown⟩
    iNamed Hown
    imodintro
    iexists γv, voted
    iframe Hvoted Hfrags
    isplitr; · ipureintro; exact Hname
    isplitr; · ipureintro; exact Hidnz
    isplitr; · ipureintro; exact voteHistOk_eq _ _ _ Hhist rfl rfl
    isplitr
    · simp only [psendMsgs, pbecomeLeader]
      iapply (BigSepL.bigSepL_append (Φ := fun _ m => isMessage (GF := GF) γ m)).2
      isplitr; · iexact Hout
      iapply isMessage_triv_list
      intro x hx; rw [(Hms x hx).1]; decide
    isplitr
    · simp only [psendMsgs, pbecomeLeader, granted_empty]
      iapply BigSepM.bigSepM_empty.2; iempintro
    · unfold leaderWit isLeader; simp only [psendMsgs, pbecomeLeader]
      iexists (granted s.votes)
      iframe Htally
      ipureintro; exact Hq
  | lose s Hrole Hnq =>
    -- back to follower in the same term, so the vote stands
    iintro _ Hown
    unfold ownRaftGhost
    icases Hown with ⟨%γv, %voted, Hown⟩
    iNamed Hown
    imodintro
    iexists γv, voted
    iframe Hvoted Hfrags
    isplitr; · ipureintro; exact Hname
    isplitr; · ipureintro; exact Hidnz
    isplitr
    · ipureintro; exact voteHistOk_eq _ _ _ Hhist rfl (pbecomeFollower_vote_same s _)
    isplitr; · simp only [pbecomeFollower]; iexact Hout
    isplitr
    · simp only [pbecomeFollower, granted_empty]
      iapply BigSepM.bigSepM_empty.2; iempintro
    · unfold leaderWit; simp only [pbecomeFollower]; iempintro
  | drain s o' Hsub =>
    -- the messages kept are messages that were there
    iintro _ Hown
    unfold ownRaftGhost
    icases Hown with ⟨%γv, %voted, Hown⟩
    iNamed Hown
    imodintro
    iexists γv, voted
    iframe Hvoted Hfrags
    isplitr; · ipureintro; exact Hname
    isplitr; · ipureintro; exact Hidnz
    isplitr; · ipureintro; exact voteHistOk_eq _ _ _ Hhist rfl rfl
    isplitr
    · simp only
      iapply bigSepL_subperm (fun m => isMessage (GF := GF) γ m) Hsub $$ Hout
    isplitr; · simp only; iexact Htally
    · unfold leaderWit; simp only; iexact Hlead

/-! ### Allocation

Nothing above says the ghost state is inhabited, and an empty `ownRaftGhost` would
make every lemma here true and useless. This is what rules that out: a fresh ghost
state for any set of nodes, each in the initial protocol state. -/

def initPState : PState where
  term := W64 0
  vote := W64 0
  lead := W64 0
  role := .follower
  votes := ∅
  outbox := []

/-- A `[∗map]` that ignores the values is one over the domain. -/
theorem bigSepM_domSet {V : Type} (m : GMap w64 V) (Φ : w64 → IProp GF) :
    ([∗map] k ↦ _v ∈ m, Φ k) ⊣⊢ [∗map] k ↦ _u ∈ toMap (domSet m), Φ k := by
  induction m using GMap.map_ind with
  | h0 =>
    rw [GMap.dom_empty_L]
    exact BigSepM.bigSepM_empty.trans BigSepM.bigSepM_empty.symm
  | hins k v m hk ih =>
    have hdom : domSet (<[k := v]> m) = <[k := ()]> (domSet m) := by
      apply GMap.ext; intro x
      by_cases hx : x = k
      · subst hx; simp
      · have : k ≠ x := Ne.symm hx
        simp [this]
    have hk' : (domSet m) !! k = none := by simp [hk]
    rw [hdom]
    exact (BigSepM.bigSepM_insert (Φ := fun k _ => Φ k) hk).trans
      ((sep_congr .rfl ih).trans (BigSepM.bigSepM_insert (Φ := fun k _ => Φ k) hk').symm)

theorem alloc_vote_maps (ids : GSet w64) :
    ⊢ |==> ∃ names : GMap w64 GName, ⌜domSet names = ids⌝ ∗
      [∗map] _γv ∈ names, ghostMapAuth (GF := GF) _γv 1 (∅ : GMap w64 w64) := by
  induction ids using GMap.set_ind_L with
  | h0 =>
    imodintro
    iexists ∅
    isplitr
    · ipureintro; exact GMap.dom_empty_L
    · iapply BigSepM.bigSepM_empty.2; iempintro
  | hins x X Hx IH =>
    imod IH with ⟨%names, %Hdom, Hm⟩
    imod ghost_map_alloc_empty (GF := GF) (K := w64) (V := w64) with ⟨%γv, Hauth⟩
    have Hnone : names !! x = none := GMap.not_elem_of_dom_1 _ _ (by rw [Hdom]; exact Hx)
    imodintro
    iexists <[x := γv]> names
    isplitr
    · ipureintro; rw [GMap.dom_insert_L, Hdom]
    · iapply (BigSepM.bigSepM_insert
        (Φ := fun _ γv => ghostMapAuth (GF := GF) γv 1 (∅ : GMap w64 w64)) Hnone).2
      iframe

theorem ownRaftGhost_alloc (cfg ids : GSet w64) (Hnz : W64 0 ∉ ids) :
    ⊢ |==> ∃ γ : RaftElectionNames, ⌜γ.reCfg = cfg⌝ ∗
      [∗map] id ↦ _u ∈ (toMap ids), ownRaftGhost (GF := GF) γ id initPState := by
  imod alloc_vote_maps (GF := GF) ids with ⟨%names, %Hdom, Hm⟩
  imodintro
  iexists ⟨cfg, names⟩
  isplitr
  · ipureintro; rfl
  rw [← Hdom]
  iapply (bigSepM_domSet names (fun id => ownRaftGhost (GF := GF) ⟨cfg, names⟩ id initPState)).1
  iapply BigSepM.bigSepM_impl $$ Hm
  imodintro
  iintro %k %γv %Hlook Hauth
  unfold ownRaftGhost
  iexists γv, ∅
  isplitr; · ipureintro; exact Hlook
  isplitr
  · ipureintro
    intro hk; subst hk; apply Hnz; rw [← Hdom]
    exact GMap.elem_of_dom_2 _ _ _ Hlook
  isplitl [Hauth]; · iexact Hauth
  isplitr
  · ipureintro
    refine ⟨fun t ht => by simp at ht, by simp [initPState]⟩
  isplitr; · iapply BigSepM.bigSepM_empty.2; iempintro
  isplitr
  · simp only [initPState]
    iapply (BigSepL.bigSepL_nil (Φ := fun _ m => isMessage (GF := GF) ⟨cfg, names⟩ m)).2; iempintro
  isplitr
  · simp only [initPState, granted_empty]; iapply BigSepM.bigSepM_empty.2; iempintro
  · unfold leaderWit; simp only [initPState]; iempintro

/-! ## Derived conveniences used by `Election.lean` -/

/-- Taking a step that consumes a single known message. -/
theorem ownRaftGhost_step_1 (γ : RaftElectionNames) (id : w64) (s : PState) (m : Msg)
    (s' : PState) (Hstep : Step γ.reCfg id s [m] s') :
    ⊢ isMessage (GF := GF) γ m -∗ ownRaftGhost γ id s ={⊤}=∗ ownRaftGhost γ id s' := by
  iintro #Hm Hown
  iapply ownRaftGhost_step γ id s [m] s' Hstep $$ [] Hown
  iapply (BigSepL.bigSepL_singleton (Φ := fun _ m => isMessage (GF := GF) γ m)).2
  iexact Hm

/-- Taking a step that consumes nothing. -/
theorem ownRaftGhost_step_0 (γ : RaftElectionNames) (id : w64) (s s' : PState)
    (Hstep : Step γ.reCfg id s [] s') :
    ⊢ ownRaftGhost (GF := GF) γ id s ={⊤}=∗ ownRaftGhost γ id s' := by
  iintro Hown
  iapply ownRaftGhost_step γ id s [] s' Hstep $$ [] Hown
  iapply (BigSepL.bigSepL_nil (Φ := fun _ m => isMessage (GF := GF) γ m)).2
  iempintro

end step

end EtcdGrove
end Perennial
