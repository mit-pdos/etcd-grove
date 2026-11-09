/-
Lean-first (no Rocq counterpart). Trace-check's S5, route (b) (2026-11-09): the specification
invariants `LeaderEntries`, `DurInv` and `CommitWithinLeader` (`TraceSimFacts.lean`) are preserved
by the actions of `etcdraft.tla` the traces take, through a strengthened invariant `SpecInv`.

Scope: no `PreVote`, no `CheckQuorum`, a fixed server set; no restart, configuration change,
snapshot, duplicate or drop. Each action's lemma takes the action's acting servers in the server
set, the message it handles in `messages` with the `Receive` dispatch's facts (its type, its
source and destination), and, where the specification's state does not record what preservation
needs, an explicit hypothesis named `h…` and documented in the lemma's docstring: what the
simulation supplies from raft's ghost state.

`SpecInv` is `LeaderEntries ∧ DurS ∧ TermsLe ∧ CandS ∧ PrevOk ∧ CommitInDurable ∧ ReqCommit ∧
ReqCommitC ∧ LeaderDurPrefix ∧ LogTermsLe ∧ CfgFixed`: `DurS` strengthens `DurInv` (a leader's
durable log within its log, the pending requests and acknowledgements within its log), `CandS` is a
candidate's (no append request or acknowledgement of its term; persisted once anything of its term
has left it), `TermsLe` and `PrevOk` are the messages', `CommitInDurable` strengthens
`CommitWithinLeader` (a server's commit index within its term's leader's durable log), `ReqCommit`
and `ReqCommitC` the append requests' commit indices (within their term's leader's durable log;
within their sender's commit index), `LeaderDurPrefix` a leader's durable log (it holds the entries
of the earlier terms: its log when it was elected, persisted), `LogTermsLe` the entries' terms
(within their server's term, their message's term), `CfgFixed` the configurations (every server's
the server set, review round 4's D1; `ApplySimpleConfChange` reapplying it keeps it,
`specInv_applySimpleConfChange`). It gives `LeaderEntries`, `CommitWithinLeader`,
`ElectionSafetyInv`, `CommittedIsDurableInv` and `DurInvFixed`, but not `DurInv`, which is not an
invariant (`durInv_not_preserved`).

The hypotheses the simulation supplies:
- `MoreThanOneLeaderInv` of the state (`ClientRequest`, `AdvanceCommitIndex`, `AppendEntries`,
  `Heartbeat`);
- `BecomeLeader`: no entry and no append request of the new leader's term yet, and every server of
  its term with its commit index within the new leader's log (leader completeness);
- `UpdateTerm`, `Timeout`: `LeaderComplete`, the server's committed entries in the log of any leader
  of its new term (leader completeness, `allFacts_leaderCompleteness`, and `CommitOk`,
  `allFacts_commitOk`), which with `LeaderDurPrefix` and `LogTermsLe` puts its commit index within
  that leader's durable log (`commitInDurable_of_complete`);
- `AppendEntries`: `b ≤ Len(log[i]) + 1`, as `NextAsync` enumerates.

`AppendEntriesAlreadyDone` needs none: the acknowledged commit index is within the leader's durable
log by `CommitInDurable` (review round 3's B6(b)).

`QuorumLogS` restates `TracedHooksDraft`'s `QuorumLogF` (equal by `rfl`: `QuorumLogF_eq` there);
`quorumLog_appendEntriesAlreadyDone` re-establishes it when a follower's commit index rises (review
round 3's B6(a)), from `ReqCommitC`, `CfgFixed` (the sender's quorum condition is over the
receiver's configuration) and the post-state's committed prefixes (`allFacts_logInv`).
-/
module

public import Proof.go_etcd_io.raft.v3.TraceSimFacts

@[expose] public section

set_option autoImplicit false

namespace Perennial
namespace EtcdGrove
namespace TraceSpecInv

open Etcdraft

variable [GooseExts]

/-! ## The strengthened invariant -/

/-- Both bags' messages. -/
def msgs (σ : State) : List Etcdraft.Msg := σ.messages.domain ++ σ.pendingMessages.domain

/-- A server's log is persisted (its durable log as long as its log). -/
def persisted (v : Server) : Prop := v.durable.log.length = v.log.length

/-- A message's terms: within its source's term, and, a granted vote or a successful append
response, within its destination's term (it answers a request of the destination's). -/
def MsgTermOk (σ : State) (m : Etcdraft.Msg) : Prop :=
  m.term ≤ (σ.s m.source).currentTerm ∧
  ((m.type = .requestVoteResponse ∧ m.voteGranted = true) ∨
      (m.type = .appendEntriesResponse ∧ m.success = true) →
    m.term ≤ (σ.s m.dest).currentTerm)

/-- Every message's terms. -/
def TermsLe (σ : State) : Prop := ∀ m ∈ msgs σ, MsgTermOk σ m

/-- A message carrying entries has a non-negative previous index. -/
def PrevOk (σ : State) : Prop := ∀ m ∈ msgs σ, m.entries ≠ [] → 0 ≤ m.prevLogIndex

/-- **A leader's durable bound**, strengthened from `DurInv`: for every leader `i` of term `T`, its
durable log no longer than its log (a leader's log only grows; a candidate persisted it), and
its commit index, its match indices, its term-`T` append requests in `messages` (handed out by a
`Ready`, after persisting) and the successful term-`T` responses addressed to it in `messages`
within its durable log; those still pending within its log, a pending response from another
server within its durable log (it answers a request handed out). -/
def DurS (σ : State) : Prop :=
  ∀ i ∈ σ.server, (σ.s i).state = leader →
    ((σ.s i).durable.log.length : Int) ≤ (σ.s i).log.length ∧
    (σ.s i).commitIndex ≤ (σ.s i).durable.log.length ∧
    (∀ j ∈ σ.server, (σ.s i).matchIndex j ≤ (σ.s i).durable.log.length) ∧
    (∀ m ∈ σ.messages.domain, m.source = i → m.type = .appendEntriesRequest →
      m.term = (σ.s i).currentTerm → m.prevLogIndex + m.entries.length ≤ (σ.s i).durable.log.length) ∧
    (∀ m ∈ σ.pendingMessages.domain, m.source = i → m.type = .appendEntriesRequest →
      m.term = (σ.s i).currentTerm → m.prevLogIndex + m.entries.length ≤ (σ.s i).log.length) ∧
    (∀ m ∈ σ.messages.domain, m.dest = i → m.type = .appendEntriesResponse →
      m.term = (σ.s i).currentTerm → m.success = true → m.matchIndex ≤ (σ.s i).durable.log.length) ∧
    (∀ m ∈ σ.pendingMessages.domain, m.dest = i → m.type = .appendEntriesResponse →
      m.term = (σ.s i).currentTerm → m.success = true →
      m.matchIndex ≤ (σ.s i).log.length ∧ (m.source ≠ i → m.matchIndex ≤ (σ.s i).durable.log.length))

/-- **A candidate's messages**: a candidate of term `T` has no append request of term `T` out and
no successful append response of term `T` addressed to it; and either it has persisted its log, or
nothing of its term has left it yet: no vote granted, nothing of term `T` from it in `messages`, no
granted vote of term `T` for it in `messages`, and the pending ones its own. -/
def CandS (σ : State) : Prop :=
  ∀ i ∈ σ.server, (σ.s i).state = candidate →
    (∀ m ∈ msgs σ, m.source = i → m.type = .appendEntriesRequest → m.term < (σ.s i).currentTerm) ∧
    (∀ m ∈ msgs σ, m.dest = i → m.type = .appendEntriesResponse → m.success = true →
      m.term < (σ.s i).currentTerm) ∧
    (persisted (σ.s i) ∨
      ((σ.s i).votesGranted = [] ∧
        (∀ m ∈ σ.messages.domain, m.source = i → m.term < (σ.s i).currentTerm) ∧
        (∀ m ∈ σ.messages.domain, m.dest = i → m.type = .requestVoteResponse → m.voteGranted = true →
          m.term < (σ.s i).currentTerm) ∧
        (∀ m ∈ σ.pendingMessages.domain, m.dest = i → m.type = .requestVoteResponse →
          m.voteGranted = true → m.term = (σ.s i).currentTerm → m.source = i)))

/-- **A server's commit index within its term's leader's durable log** (strengthens
`CommitWithinLeader`: a leader's durable log is within its log, `DurS`). The commit index rises by a
leader's quorum (within its durable log, `DurS`) or by an append request of the term (`ReqCommit`);
a server entering a term with a leader has its committed entries in the leader's log at its election,
persisted (`LeaderDurPrefix`). -/
def CommitInDurable (σ : State) : Prop :=
  ∀ i ∈ σ.server, ∀ l ∈ σ.server, (σ.s l).state = leader →
    (σ.s i).currentTerm = (σ.s l).currentTerm → (σ.s i).commitIndex ≤ (σ.s l).durable.log.length

/-- **The append requests' commit indices**: an append request of a leader's term carries a commit
index within that leader's durable log (only the term's leader sends them, with its commit index, within
its durable log by `DurS`; a leader's durable log only grows). -/
def ReqCommit (σ : State) : Prop :=
  ∀ l ∈ σ.server, (σ.s l).state = leader → ∀ m ∈ msgs σ, m.type = .appendEntriesRequest →
    m.term = (σ.s l).currentTerm → m.commitIndex ≤ (σ.s l).durable.log.length

/-- **An append request's commit index within its sender's** (review round 3's B6(a)): its sender is a
server and the request carries at most its commit index then; a commit index only grows. -/
def ReqCommitC (σ : State) : Prop :=
  ∀ m ∈ msgs σ, m.type = .appendEntriesRequest →
    m.source ∈ σ.server ∧ m.commitIndex ≤ (σ.s m.source).commitIndex

/-- **A leader's durable log holds its entries of the earlier terms** (review round 3's B6(b)): they
are its log when it was elected, which it had persisted (`CandS`), and it only appends after. -/
def LeaderDurPrefix (σ : State) : Prop :=
  ∀ l ∈ σ.server, (σ.s l).state = leader → ∀ (k : Nat) (e : Entry), (σ.s l).log[k]? = some e →
    e.term < (σ.s l).currentTerm → (k : Int) < (σ.s l).durable.log.length

/-- **The entries' terms**: within their server's term, and a message's within the message's term. -/
def LogTermsLe (σ : State) : Prop :=
  (∀ k ∈ σ.server, ∀ e ∈ (σ.s k).log, e.term ≤ (σ.s k).currentTerm) ∧
  (∀ m ∈ msgs σ, ∀ e ∈ m.entries, e.term ≤ m.term)

/-- **Every server's configuration is the fixed voter configuration** (review round 4's D1): the
server set, no outgoing configuration, no learners. `simInit` sets it (its server set is the voters'
`confAbs C`); no action in scope changes a configuration (`ApplySimpleConfChange` under the
simulation's `AccIdle` reapplies the same one, `specInv_applySimpleConfChange`; `reconfigure` is out
of scope). -/
def CfgFixed (σ : State) : Prop :=
  ∀ j ∈ σ.server, (σ.s j).config = { incoming := σ.server, outgoing := [], learners := [] }

/-- **The strengthened invariant.** -/
def SpecInv (σ : State) : Prop :=
  LeaderEntries σ ∧ DurS σ ∧ TermsLe σ ∧ CandS σ ∧ PrevOk σ ∧ CommitInDurable σ ∧ ReqCommit σ ∧
    ReqCommitC σ ∧ LeaderDurPrefix σ ∧ LogTermsLe σ ∧ CfgFixed σ

/-- `DurInv` with the pending self-acknowledgements left out (`DurInv` itself is not an invariant:
`appendEntriesToSelf` puts a response with the leader's log length, possibly past its durable
log, in `pendingMessages`; `durInv_not_preserved`). -/
def DurInvFixed (σ : State) : Prop :=
  ∀ i ∈ σ.server, (σ.s i).state = leader →
    let d : Int := (σ.s i).durable.log.length
    (σ.s i).commitIndex ≤ d ∧ (∀ j ∈ σ.server, (σ.s i).matchIndex j ≤ d) ∧
    (∀ m ∈ σ.messages.domain, m.source = i → m.type = .appendEntriesRequest →
      m.term = (σ.s i).currentTerm → m.prevLogIndex + m.entries.length ≤ d) ∧
    (∀ m ∈ σ.messages.domain ++ σ.pendingMessages.domain, m.dest = i → m.type = .appendEntriesResponse →
      m.term = (σ.s i).currentTerm → m.success = true → (m ∈ σ.pendingMessages.domain → m.source ≠ i) →
      m.matchIndex ≤ d)

theorem SpecInv.leaderEntries {σ : State} (h : SpecInv σ) : LeaderEntries σ := h.1

theorem SpecInv.commitInDurable {σ : State} (h : SpecInv σ) : CommitInDurable σ := h.2.2.2.2.2.1

theorem SpecInv.reqCommit {σ : State} (h : SpecInv σ) : ReqCommit σ := h.2.2.2.2.2.2.1

theorem SpecInv.reqCommitC {σ : State} (h : SpecInv σ) : ReqCommitC σ := h.2.2.2.2.2.2.2.1

theorem SpecInv.leaderDurPrefix {σ : State} (h : SpecInv σ) : LeaderDurPrefix σ := h.2.2.2.2.2.2.2.2.1

theorem SpecInv.logTermsLe {σ : State} (h : SpecInv σ) : LogTermsLe σ := h.2.2.2.2.2.2.2.2.2.1

theorem SpecInv.cfgFixed {σ : State} (h : SpecInv σ) : CfgFixed σ := h.2.2.2.2.2.2.2.2.2.2

/-- Two servers' configurations agree: both are the fixed one. -/
theorem SpecInv.getConfig_eq {σ : State} (h : SpecInv σ) {i j : ID} (hi : i ∈ σ.server)
    (hj : j ∈ σ.server) : σ.getConfig i = σ.getConfig j := by
  simp only [State.getConfig, h.cfgFixed i hi, h.cfgFixed j hj]

/-- `CfgFixed` of states with the same servers and configurations. -/
theorem cfgFixed_congr {σ σ' : State} (h : CfgFixed σ) (hsrv : σ'.server = σ.server)
    (hG : ∀ j, (σ'.s j).config = (σ.s j).config) : CfgFixed σ' := by
  intro j hj; rw [hsrv] at hj ⊢; rw [hG]; exact h j hj

/-- `CfgFixed` after an update of one server that keeps its configuration. -/
theorem cfgFixed_upd {σ : State} {i : ID} {f : Server → Server} (h : CfgFixed σ)
    (hG : (f (σ.s i)).config = (σ.s i).config) : CfgFixed (σ.upd i f) :=
  cfgFixed_congr h rfl (fun j => by
    show (if j = i then f (σ.s i) else σ.s j).config = _
    split <;> subst_vars <;> first | exact hG | rfl)

theorem SpecInv.commitWithinLeader {σ : State} (h : SpecInv σ) : CommitWithinLeader σ :=
  fun i hi l hl hll ht => Int.le_trans (h.commitInDurable i hi l hl hll ht) (h.2.1 l hl hll).1

theorem SpecInv.durInvFixed {σ : State} (h : SpecInv σ) : DurInvFixed σ := by
  intro i hi hl
  obtain ⟨-, hc, hmi, hrq, -, hrm, hrp⟩ := h.2.1 i hi hl
  refine ⟨hc, fun j hj => hmi j hj, hrq, ?_⟩
  intro m hm hd ht htm hs hp
  rcases List.mem_append.mp hm with hm | hm
  · exact hrm m hm hd ht htm hs
  · exact (hrp m hm hd ht htm hs).2 (hp hm)

/-- `CommittedIsDurableInv` from the strengthened invariant. -/
theorem SpecInv.committedIsDurable {σ : State} (h : SpecInv σ) : σ.committedIsDurableInv = true := by
  unfold State.committedIsDurableInv
  rw [List.all_eq_true]
  intro i hi
  by_cases hl : (σ.s i).state = leader
  · simp [hl, (h.2.1 i hi hl).2.1]
  · simp [hl]

/-- `ElectionSafetyInv` from the strengthened invariant. -/
theorem SpecInv.electionSafety {σ : State} (h : SpecInv σ) : σ.electionSafetyInv = true :=
  electionSafety_of_leaderEntries σ h.1

/-! ## Bags -/

theorem mem_with (b : Bag) (m x : Etcdraft.Msg) : x ∈ (b.with m).domain ↔ x ∈ b.domain ∨ x = m := by
  unfold Bag.with Bag.add Bag.domain
  split
  · rename_i h
    rw [List.any_eq_true] at h
    obtain ⟨it, hit, he⟩ := h
    simp only [beq_iff_eq] at he
    have : (b.map fun it => if it.1 = m then (it.1, it.2 + 1) else it).map Prod.fst = b.map Prod.fst := by
      rw [List.map_map]; congr 1; funext it; simp only [Function.comp]; split <;> rfl
    simp only [beq_iff_eq]
    rw [this]
    constructor
    · exact Or.inl
    · rintro (h | rfl)
      · exact h
      · exact List.mem_map.mpr ⟨it, hit, he⟩
  · simp

theorem mem_without (b : Bag) (m x : Etcdraft.Msg) (h : x ∈ (b.without m).domain) : x ∈ b.domain := by
  unfold Bag.without Bag.sub Bag.domain at h
  unfold Bag.domain
  obtain ⟨it, hit, rfl⟩ := List.mem_map.mp h
  obtain ⟨it0, hit0, he⟩ := List.mem_filterMap.mp hit
  refine List.mem_map.mpr ⟨it0, hit0, ?_⟩
  split at he
  · split at he
    · cases he; rfl
    · cases he
  · cases he; rfl

theorem mem_sub (b : Bag) (m : Etcdraft.Msg) (n : Nat) (x : Etcdraft.Msg) (h : x ∈ (b.sub m n).domain) : x ∈ b.domain := by
  unfold Bag.sub Bag.domain at h
  unfold Bag.domain
  obtain ⟨it, hit, rfl⟩ := List.mem_map.mp h
  obtain ⟨it0, hit0, he⟩ := List.mem_filterMap.mp hit
  refine List.mem_map.mpr ⟨it0, hit0, ?_⟩
  split at he
  · split at he
    · cases he; rfl
    · cases he
  · cases he; rfl

theorem mem_add (b : Bag) (m : Etcdraft.Msg) (n : Nat) (x : Etcdraft.Msg) (h : x ∈ (b.add m n).domain) :
    x ∈ b.domain ∨ x = m := by
  unfold Bag.add Bag.domain at h
  unfold Bag.domain
  split at h
  · obtain ⟨it, hit, rfl⟩ := List.mem_map.mp h
    obtain ⟨it0, hit0, he⟩ := List.mem_map.mp hit
    left
    refine List.mem_map.mpr ⟨it0, hit0, ?_⟩
    split at he <;> (subst he; rfl)
  · simpa using h

theorem mem_plus (b c : Bag) (x : Etcdraft.Msg) (h : x ∈ (b.plus c).domain) : x ∈ b.domain ∨ x ∈ c.domain := by
  unfold Bag.plus at h
  induction c generalizing b with
  | nil => exact Or.inl h
  | cons it c ih =>
    rw [List.foldl_cons] at h
    rcases ih _ h with h | h
    · rcases mem_add b it.1 it.2 x h with h | rfl
      · exact Or.inl h
      · right; simp [Bag.domain]
    · right; unfold Bag.domain at h ⊢; simp only [List.map_cons, List.mem_cons]; exact Or.inr h

theorem mem_minus (b c : Bag) (x : Etcdraft.Msg) (h : x ∈ (b.minus c).domain) : x ∈ b.domain := by
  unfold Bag.minus at h
  induction c generalizing b with
  | nil => exact h
  | cons it c ih =>
    rw [List.foldl_cons] at h
    exact mem_sub b it.1 it.2 x (ih _ h)

theorem mem_filterMsgs (b : Bag) (p : Etcdraft.Msg → Bool) (x : Etcdraft.Msg) (h : x ∈ (b.filterMsgs p).domain) :
    x ∈ b.domain ∧ p x = true := by
  unfold Bag.filterMsgs Bag.domain at h
  obtain ⟨it, hit, rfl⟩ := List.mem_map.mp h
  obtain ⟨hit, hp⟩ := List.mem_filter.mp hit
  exact ⟨List.mem_map.mpr ⟨it, hit, rfl⟩, hp⟩

/-! ## Sending, discarding, and states that agree -/

/-- **What a sent message must satisfy** for `SpecInv` to hold once it is in `pendingMessages`. -/
def MsgOk (σ : State) (m : Etcdraft.Msg) : Prop :=
  (∀ i ∈ σ.server, (σ.s i).state = leader → ∀ (k : Nat) (e : Entry), m.entries[k]? = some e →
      e.term = (σ.s i).currentTerm →
      ((σ.s i).log[(m.prevLogIndex.toNat + k)]?).map Entry.term = some e.term) ∧
  (∀ i ∈ σ.server, (σ.s i).state = leader →
      (m.source = i → m.type = .appendEntriesRequest → m.term = (σ.s i).currentTerm →
        m.prevLogIndex + m.entries.length ≤ (σ.s i).log.length) ∧
      (m.dest = i → m.type = .appendEntriesResponse → m.term = (σ.s i).currentTerm → m.success = true →
        m.matchIndex ≤ (σ.s i).log.length ∧ (m.source ≠ i → m.matchIndex ≤ (σ.s i).durable.log.length)) ∧
      (m.type = .appendEntriesRequest → m.term = (σ.s i).currentTerm →
        m.commitIndex ≤ (σ.s i).durable.log.length)) ∧
  MsgTermOk σ m ∧
  (∀ i ∈ σ.server, (σ.s i).state = candidate →
      (m.source = i → m.type = .appendEntriesRequest → m.term < (σ.s i).currentTerm) ∧
      (m.dest = i → m.type = .appendEntriesResponse → m.success = true → m.term < (σ.s i).currentTerm) ∧
      (¬ persisted (σ.s i) → m.dest = i → m.type = .requestVoteResponse → m.voteGranted = true →
        m.term = (σ.s i).currentTerm → m.source = i)) ∧
  (m.entries ≠ [] → 0 ≤ m.prevLogIndex) ∧
  (∀ e ∈ m.entries, e.term ≤ m.term) ∧
  (m.type = .appendEntriesRequest → m.source ∈ σ.server ∧ m.commitIndex ≤ (σ.s m.source).commitIndex)

/-- A message with no entries that is neither an append request, a successful append response
nor a granted vote, of its source's term at most, is fine to send. -/
theorem msgOk_plain (σ : State) (m : Etcdraft.Msg) (he : m.entries = [])
    (hq : m.type ≠ .appendEntriesRequest) (hs : m.type = .appendEntriesResponse → m.success = false)
    (hv : m.type = .requestVoteResponse → m.voteGranted = false)
    (ht : m.term ≤ (σ.s m.source).currentTerm) : MsgOk σ m := by
  refine ⟨?_, ?_, ⟨ht, ?_⟩, ?_, ?_, ?_, fun h => absurd h hq⟩
  · intro i _ _ k e hk; rw [he] at hk; simp at hk
  · intro i _ _
    refine ⟨fun _ h => absurd h hq, fun _ h _ hs' => ?_, fun h => absurd h hq⟩
    rw [hs h] at hs'; cases hs'
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · rw [hv h1] at h2; cases h2
    · rw [hs h1] at h2; cases h2
  · intro i _ _
    refine ⟨fun _ h => absurd h hq, fun _ h hs' => ?_, fun _ _ h hg => ?_⟩
    · rw [hs h] at hs'; cases hs'
    · rw [hv h] at hg; cases hg
  · intro h; exact absurd he h
  · intro e h; rw [he] at h; cases h

theorem mem_msgs_send (σ : State) (m x : Etcdraft.Msg) (hx : x ∈ msgs (σ.send m)) :
    x ∈ msgs σ ∨ x = m := by
  unfold msgs at *
  rcases List.mem_append.mp hx with h | h
  · exact Or.inl (List.mem_append_left _ h)
  · rcases (mem_with _ _ _).mp h with h | h
    · exact Or.inl (List.mem_append_right _ h)
    · exact Or.inr h

/-- **`Send(m)`** keeps the invariant when `m` is fine to send. -/
theorem specInv_send {σ : State} {m : Etcdraft.Msg} (h : SpecInv σ) (hm : MsgOk σ m) :
    SpecInv (σ.send m) := by
  obtain ⟨hLE, hD, hT, hC, hP, hCW, hRC, hRCC, hLDP, ⟨hLT1, hLT2⟩, hCF⟩ := h
  obtain ⟨mLE, mD, mT, mC, mP, mE, mRCC⟩ := hm
  have hmem := mem_msgs_send σ m
  refine ⟨?_, ?_, ?_, ?_, ?_, hCW, ?_, ?_, hLDP, ⟨hLT1, ?_⟩, hCF⟩
  · intro i hi hl
    obtain ⟨h1, h2⟩ := hLE i hi hl
    refine ⟨h1, ?_⟩
    intro x hx k e hk ht
    rcases hmem x hx with hx | rfl
    · exact h2 x hx k e hk ht
    · exact mLE i hi hl k e hk ht
  · intro i hi hl
    obtain ⟨a1, a2, a3, a4, a5, a6, a7⟩ := hD i hi hl
    obtain ⟨b1, b2, -⟩ := mD i hi hl
    refine ⟨a1, a2, a3, a4, ?_, a6, ?_⟩
    · intro x hx; rcases (mem_with _ _ _).mp hx with hx | rfl
      · exact a5 x hx
      · exact b1
    · intro x hx; rcases (mem_with _ _ _).mp hx with hx | rfl
      · exact a7 x hx
      · exact b2
  · intro x hx; rcases hmem x hx with hx | rfl
    · exact hT x hx
    · exact mT
  · intro i hi hc
    obtain ⟨c1, c2, c3⟩ := hC i hi hc
    obtain ⟨d1, d2, d3⟩ := mC i hi hc
    refine ⟨fun x hx => ?_, fun x hx => ?_, ?_⟩
    · rcases hmem x hx with hx | rfl
      · exact c1 x hx
      · exact d1
    · rcases hmem x hx with hx | rfl
      · exact c2 x hx
      · exact d2
    · by_cases hp : persisted (σ.s i)
      · exact Or.inl hp
      · rcases c3 with hp' | ⟨v1, v2, v3, v4⟩
        · exact absurd hp' hp
        · refine Or.inr ⟨v1, v2, v3, fun x hx => ?_⟩
          rcases (mem_with _ _ _).mp hx with hx | rfl
          · exact v4 x hx
          · exact d3 hp
  · intro x hx; rcases hmem x hx with hx | rfl
    · exact hP x hx
    · exact mP
  · intro l hl hld x hx; rcases hmem x hx with hx | rfl
    · exact hRC l hl hld x hx
    · exact (mD l hl hld).2.2
  · intro x hx; rcases hmem x hx with hx | rfl
    · exact hRCC x hx
    · exact mRCC
  · intro x hx; rcases hmem x hx with hx | rfl
    · exact hLT2 x hx
    · exact mE

/-- **Fewer messages**: the same servers, and each bag's messages among the old ones. -/
theorem specInv_mono {σ σ' : State} (h : SpecInv σ) (hs : σ'.s = σ.s) (hsrv : σ'.server = σ.server)
    (hm : ∀ x ∈ σ'.messages.domain, x ∈ σ.messages.domain)
    (hp : ∀ x ∈ σ'.pendingMessages.domain, x ∈ σ.pendingMessages.domain) : SpecInv σ' := by
  have hmm : ∀ x ∈ msgs σ', x ∈ msgs σ := by
    intro x hx; unfold msgs at *
    rcases List.mem_append.mp hx with h | h
    · exact List.mem_append_left _ (hm x h)
    · exact List.mem_append_right _ (hp x h)
  obtain ⟨hLE, hD, hT, hC, hP, hCW, hRC, hRCC, hLDP, ⟨hLT1, hLT2⟩, hCF⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ⟨?_, ?_⟩, cfgFixed_congr hCF hsrv (fun j => by rw [hs])⟩
  · intro i hi hl
    rw [hsrv] at hi; rw [hs] at hl ⊢
    obtain ⟨h1, h2⟩ := hLE i hi hl
    refine ⟨fun j hj => h1 j (hsrv ▸ hj), fun x hx => h2 x (hmm x hx)⟩
  · intro i hi hl
    rw [hsrv] at hi; rw [hs] at hl ⊢
    obtain ⟨a1, a2, a3, a4, a5, a6, a7⟩ := hD i hi hl
    exact ⟨a1, a2, fun x hx => a3 x (by rw [hsrv] at hx; exact hx), fun x hx => a4 x (hm x hx), fun x hx => a5 x (hp x hx),
      fun x hx => a6 x (hm x hx), fun x hx => a7 x (hp x hx)⟩
  · intro x hx; unfold MsgTermOk; rw [hs]; exact hT x (hmm x hx)
  · intro i hi hc
    rw [hsrv] at hi; rw [hs] at hc ⊢
    obtain ⟨c1, c2, c3⟩ := hC i hi hc
    refine ⟨fun x hx => c1 x (hmm x hx), fun x hx => c2 x (hmm x hx), ?_⟩
    rcases c3 with hp' | ⟨v1, v2, v3, v4⟩
    · exact Or.inl hp'
    · exact Or.inr ⟨v1, fun x hx => v2 x (hm x hx), fun x hx => v3 x (hm x hx), fun x hx => v4 x (hp x hx)⟩
  · intro x hx; exact hP x (hmm x hx)
  · intro i hi l hl; rw [hsrv] at hi hl; rw [hs]; exact hCW i hi l hl
  · intro l hl hld x hx; rw [hsrv] at hl; rw [hs] at hld ⊢; exact hRC l hl hld x (hmm x hx)
  · intro x hx hty; rw [hsrv, hs]; exact hRCC x (hmm x hx) hty
  · intro l hl; rw [hsrv] at hl; rw [hs]; exact hLDP l hl
  · intro k hk; rw [hsrv] at hk; rw [hs]; exact hLT1 k hk
  · intro x hx; exact hLT2 x (hmm x hx)

/-- **`Discard(m)`.** -/
theorem specInv_discard {σ : State} (m : Etcdraft.Msg) (h : SpecInv σ) : SpecInv (σ.discard m) :=
  specInv_mono h rfl rfl (fun _ hx => mem_without _ _ _ hx) (fun _ hx => hx)

theorem reply_eq (σ : State) (r q : Etcdraft.Msg) : σ.reply r q = (σ.discard q).send r := rfl

/-- **`Reply(response, request)`** keeps the invariant when the response is fine to send. -/
theorem specInv_reply {σ : State} {r q : Etcdraft.Msg} (h : SpecInv σ) (hm : MsgOk (σ.discard q) r) :
    SpecInv (σ.reply r q) := by
  rw [reply_eq]; exact specInv_send (specInv_discard q h) hm

/-- **States that agree** on the servers, the bags' messages, and every server's fields the
invariant reads. -/
theorem specInv_congr {σ σ' : State} (h : SpecInv σ) (hsrv : σ'.server = σ.server)
    (hm : σ'.messages.domain = σ.messages.domain) (hp : σ'.pendingMessages.domain = σ.pendingMessages.domain)
    (hT : ∀ j, (σ'.s j).currentTerm = (σ.s j).currentTerm) (hS : ∀ j, (σ'.s j).state = (σ.s j).state)
    (hL : ∀ j, (σ'.s j).log = (σ.s j).log) (hD : ∀ j, (σ'.s j).durable = (σ.s j).durable)
    (hV : ∀ j, (σ'.s j).votesGranted = (σ.s j).votesGranted)
    (hC : ∀ j, (σ'.s j).commitIndex = (σ.s j).commitIndex)
    (hM : ∀ j, (σ'.s j).matchIndex = (σ.s j).matchIndex)
    (hG : ∀ j, (σ'.s j).config = (σ.s j).config) : SpecInv σ' := by
  simp only [SpecInv, LeaderEntries, DurS, TermsLe, MsgTermOk, CandS, PrevOk, CommitInDurable,
    ReqCommit, ReqCommitC, LeaderDurPrefix, LogTermsLe, CfgFixed, msgs, persisted, hsrv, hm, hp, hT, hS, hL,
    hD, hV, hC, hM, hG]
  exact h

/-- **A server's update that changes none of the fields the invariant reads** (its vote, its
known leader, the votes it has had answered). -/
theorem specInv_upd_frame {σ : State} {i : ID} {f : Server → Server} (h : SpecInv σ)
    (hT : (f (σ.s i)).currentTerm = (σ.s i).currentTerm) (hS : (f (σ.s i)).state = (σ.s i).state)
    (hL : (f (σ.s i)).log = (σ.s i).log) (hD : (f (σ.s i)).durable = (σ.s i).durable)
    (hV : (f (σ.s i)).votesGranted = (σ.s i).votesGranted)
    (hC : (f (σ.s i)).commitIndex = (σ.s i).commitIndex)
    (hM : (f (σ.s i)).matchIndex = (σ.s i).matchIndex)
    (hG : (f (σ.s i)).config = (σ.s i).config) : SpecInv (σ.upd i f) := by
  apply specInv_congr (σ' := σ.upd i f) h rfl rfl rfl <;> intro j <;> simp only [State.upd] <;> split <;> subst_vars <;>
    first | assumption | rfl


/-! ## Updates of one server -/

theorem upd_s (σ : State) (i : ID) (f : Server → Server) (j : ID) :
    (σ.upd i f).s j = if j = i then f (σ.s i) else σ.s j := rfl

theorem upd_s_self (σ : State) (i : ID) (f : Server → Server) : (σ.upd i f).s i = f (σ.s i) := by
  simp [upd_s]

theorem upd_s_ne (σ : State) (i : ID) (f : Server → Server) (j : ID) (h : j ≠ i) :
    (σ.upd i f).s j = σ.s j := by
  simp [upd_s, h]

theorem follower_ne_leader : follower ≠ leader := by decide
theorem follower_ne_candidate : follower ≠ candidate := by decide
theorem candidate_ne_leader : candidate ≠ leader := by decide

/-- `MoreThanOneLeaderInv`: two leaders of one term are one server. -/
theorem oneLeader {σ : State} (h : σ.moreThanOneLeaderInv = true) {i j : ID} (hi : i ∈ σ.server)
    (hj : j ∈ σ.server) (hli : (σ.s i).state = leader) (hlj : (σ.s j).state = leader)
    (ht : (σ.s i).currentTerm = (σ.s j).currentTerm) : i = j := by
  unfold State.moreThanOneLeaderInv at h
  rw [List.all_eq_true] at h
  have := h i hi
  rw [List.all_eq_true] at this
  have := this j hj
  simpa [ht, hli, hlj] using this

/-- **A server becoming a follower or a candidate**, of its term or a later one, its log and commit
index kept; `hcw`: its commit index within the durable log of any leader of its new term (for its own
term, from `CommitInDurable`; for a later one, `commitInDurable_of_complete`); `hcand`: a candidate,
its messages as `CandS` says. -/
theorem specInv_upd_nonleader {σ : State} {i : ID} {f : Server → Server} (h : SpecInv σ)
    (hS : (f (σ.s i)).state ≠ leader) (hT : (σ.s i).currentTerm ≤ (f (σ.s i)).currentTerm)
    (hL : (f (σ.s i)).log = (σ.s i).log) (hC : (f (σ.s i)).commitIndex = (σ.s i).commitIndex)
    (hG : (f (σ.s i)).config = (σ.s i).config)
    (hcw : ∀ l ∈ σ.server, l ≠ i → (σ.s l).state = leader →
      (σ.s l).currentTerm = (f (σ.s i)).currentTerm → (σ.s i).commitIndex ≤ (σ.s l).durable.log.length)
    (hcand : (f (σ.s i)).state = candidate →
      (∀ m ∈ msgs σ, m.source = i → m.type = .appendEntriesRequest → m.term < (f (σ.s i)).currentTerm) ∧
      (∀ m ∈ msgs σ, m.dest = i → m.type = .appendEntriesResponse → m.success = true →
        m.term < (f (σ.s i)).currentTerm) ∧
      (persisted (f (σ.s i)) ∨
        ((f (σ.s i)).votesGranted = [] ∧
          (∀ m ∈ σ.messages.domain, m.source = i → m.term < (f (σ.s i)).currentTerm) ∧
          (∀ m ∈ σ.messages.domain, m.dest = i → m.type = .requestVoteResponse → m.voteGranted = true →
            m.term < (f (σ.s i)).currentTerm) ∧
          (∀ m ∈ σ.pendingMessages.domain, m.dest = i → m.type = .requestVoteResponse →
            m.voteGranted = true → m.term = (f (σ.s i)).currentTerm → m.source = i)))) :
    SpecInv (σ.upd i f) := by
  obtain ⟨hLE, hD, hTm, hCa, hP, hCW, hRC, hRCC, hLDP, ⟨hLT1, hLT2⟩, hCF⟩ := h
  have hlog : ∀ j, ((σ.upd i f).s j).log = (σ.s j).log := by
    intro j; by_cases hj : j = i
    · subst hj; rw [upd_s_self, hL]
    · rw [upd_s_ne _ _ _ _ hj]
  have hterm : ∀ j, (σ.s j).currentTerm ≤ ((σ.upd i f).s j).currentTerm := by
    intro j; by_cases hj : j = i
    · subst hj; rw [upd_s_self]; exact hT
    · rw [upd_s_ne _ _ _ _ hj]; exact Int.le_refl _
  -- a leader of the new state is not `i`
  have hne : ∀ l, ((σ.upd i f).s l).state = leader → l ≠ i := by
    rintro l hl rfl
    rw [upd_s_self] at hl
    exact hS hl
  have hcom : ∀ j, ((σ.upd i f).s j).commitIndex = (σ.s j).commitIndex := by
    intro j; by_cases hj : j = i
    · subst hj; rw [upd_s_self, hC]
    · rw [upd_s_ne _ _ _ _ hj]
  refine ⟨?_, ?_, ?_, ?_, hP, ?_, ?_, ?_, ?_, ⟨?_, hLT2⟩, cfgFixed_upd hCF hG⟩
  · intro l hl hll
    have e := upd_s_ne σ i f l (hne l hll)
    rw [e] at hll ⊢
    obtain ⟨h1, h2⟩ := hLE l hl hll
    exact ⟨fun j hj k x hx ht => h1 j hj k x (by rw [← hlog j]; exact hx) ht, h2⟩
  · intro l hl hll
    have e := upd_s_ne σ i f l (hne l hll)
    rw [e] at hll ⊢
    exact hD l hl hll
  · intro x hx
    obtain ⟨t1, t2⟩ := hTm x hx
    exact ⟨Int.le_trans t1 (hterm _), fun hh => Int.le_trans (t2 hh) (hterm _)⟩
  · intro l hl hll
    by_cases hli : l = i
    · subst hli
      rw [upd_s_self] at hll ⊢
      exact hcand hll
    · have e := upd_s_ne σ i f l hli
      rw [e] at hll ⊢
      exact hCa l hl hll
  · intro k hk l hl hll ht
    have hli := hne l hll
    have e := upd_s_ne σ i f l hli
    rw [e] at hll ht ⊢
    by_cases hki : k = i
    · subst hki
      rw [upd_s_self] at ht ⊢
      rw [hC]; exact hcw l hl hli hll ht.symm
    · rw [upd_s_ne _ _ _ _ hki] at ht ⊢
      exact hCW k hk l hl hll ht
  · intro l hl hll
    have e := upd_s_ne σ i f l (hne l hll)
    rw [e] at hll ⊢
    exact hRC l hl hll
  · intro x hx hty; rw [hcom]; exact hRCC x hx hty
  · intro l hl hll
    have e := upd_s_ne σ i f l (hne l hll)
    rw [e] at hll ⊢
    exact hLDP l hl hll
  · intro k hk e he
    rw [hlog] at he
    exact Int.le_trans (hLT1 k hk e he) (hterm k)

/-- **A server becoming a follower.** -/
theorem specInv_upd_follower {σ : State} {i : ID} {f : Server → Server} (h : SpecInv σ)
    (hS : (f (σ.s i)).state = follower) (hT : (σ.s i).currentTerm ≤ (f (σ.s i)).currentTerm)
    (hL : (f (σ.s i)).log = (σ.s i).log) (hC : (f (σ.s i)).commitIndex = (σ.s i).commitIndex)
    (hG : (f (σ.s i)).config = (σ.s i).config)
    (hcw : ∀ l ∈ σ.server, l ≠ i → (σ.s l).state = leader →
      (σ.s l).currentTerm = (f (σ.s i)).currentTerm → (σ.s i).commitIndex ≤ (σ.s l).durable.log.length) :
    SpecInv (σ.upd i f) :=
  specInv_upd_nonleader h (by rw [hS]; exact follower_ne_leader) hT hL hC hG hcw
    (fun hc => absurd (hS.symm.trans hc) follower_ne_candidate)

/-- **Leader completeness at a server `i` entering the term `t`** (what `UpdateTerm` and `Timeout` take
of the simulation; with it `AppendEntriesAlreadyDone` needs no `CommitInSenderDurable`, review round
3's B6(b)): `i`'s commit index within its log (`CommitOk`, `allFacts_commitOk`), and each committed
entry of `i` of a term below that of a leader of term `t` at the same position of that leader's log
(`allFacts_leaderCompleteness`, `t` above `i`'s term). -/
def LeaderComplete (σ : State) (i : ID) (t : Int) : Prop :=
  (σ.s i).commitIndex ≤ (σ.s i).log.length ∧
  ∀ l ∈ σ.server, (σ.s l).state = leader → (σ.s l).currentTerm = t →
    ∀ idx0 < (TraceSim.committedL σ i).length,
      (σ.s l).currentTerm > (((σ.s i).log[idx0]?).getD default).term →
      (σ.s l).log[idx0]? = some (((σ.s i).log[idx0]?).getD default)

/-- **A server entering a later term has its commit index within the durable log of the term's
leader**: its last committed entry, of a term at most its own (`LogTermsLe`), is in the leader's log
(`LeaderComplete`), where it is of an earlier term than the leader's, so durable
(`LeaderDurPrefix`). -/
theorem commitInDurable_of_complete {σ : State} {i : ID} {t : Int} (h : SpecInv σ) (hi : i ∈ σ.server)
    (ht : (σ.s i).currentTerm < t) (hlc : LeaderComplete σ i t) :
    ∀ l ∈ σ.server, (σ.s l).state = leader → (σ.s l).currentTerm = t →
      (σ.s i).commitIndex ≤ (σ.s l).durable.log.length := by
  intro l hl hll hlt
  obtain ⟨hco, hlc⟩ := hlc
  by_cases h0 : (σ.s i).commitIndex ≤ 0
  · omega
  · have hk : (σ.s i).commitIndex.toNat - 1 < (σ.s i).log.length := by omega
    obtain ⟨e, he⟩ : ∃ e, (σ.s i).log[(σ.s i).commitIndex.toNat - 1]? = some e :=
      ⟨_, List.getElem?_eq_getElem hk⟩
    have het : e.term ≤ (σ.s i).currentTerm := h.logTermsLe.1 i hi e (List.mem_of_getElem? he)
    have hin : (σ.s i).commitIndex.toNat - 1 < (TraceSim.committedL σ i).length := by
      unfold TraceSim.committedL; rw [List.length_take]; omega
    have hgt : (σ.s l).currentTerm > (((σ.s i).log[(σ.s i).commitIndex.toNat - 1]?).getD default).term := by
      rw [he]; simp only [Option.getD_some]; omega
    have := hlc l hl hll hlt _ hin hgt
    rw [he] at this; simp only [Option.getD_some] at this
    have hd := h.leaderDurPrefix l hl hll _ e this (by omega)
    omega

/-- **`BecomeFollowerOfTerm(i, t)`** for a term `t` no lower than `i`'s; `hcw`: `i`'s commit index
within the durable log of any other leader of term `t` (for `t` `i`'s own term it is
`CommitInDurable`'s; for a later one `commitInDurable_of_complete`'s). -/
theorem specInv_becomeFollowerOfTerm {σ : State} {i : ID} {t : Int} (h : SpecInv σ)
    (ht : (σ.s i).currentTerm ≤ t)
    (hcw : ∀ l ∈ σ.server, l ≠ i → (σ.s l).state = leader → (σ.s l).currentTerm = t →
      (σ.s i).commitIndex ≤ (σ.s l).durable.log.length) :
    SpecInv (σ.becomeFollowerOfTerm i t) :=
  specInv_upd_follower h rfl ht rfl rfl rfl hcw

/-- **`StepDownToFollower(i)`.** -/
theorem specInv_stepDownToFollower {σ σ' : State} {i : ID} (h : SpecInv σ) (hi : i ∈ σ.server)
    (hstep : σ.stepDownToFollower i = some σ') : SpecInv σ' := by
  unfold State.stepDownToFollower at hstep; dsimp only at hstep
  split at hstep
  · cases hstep
    exact specInv_becomeFollowerOfTerm h (Int.le_refl _) (fun l hl _ hll ht => h.commitInDurable i hi l hl hll ht.symm)
  · cases hstep

/-- **`UpdateTerm(i, j, m)`**; `hlc`: `LeaderComplete` at `m`'s term (raft: leader completeness, the
committed entries are in every later leader's log). -/
theorem specInv_updateTerm {σ σ' : State} {i j : ID} {m : Etcdraft.Msg} (h : SpecInv σ) (hi : i ∈ σ.server)
    (hlc : LeaderComplete σ i m.term)
    (hstep : σ.updateTerm i j m = some σ') : SpecInv σ' := by
  unfold State.updateTerm at hstep
  split at hstep
  · cases hstep
  · cases hstep
    rename_i hc
    have : (σ.s i).currentTerm < m.term := by
      refine Classical.byContradiction (fun hlt => hc ?_)
      simp [hlt]
    exact specInv_becomeFollowerOfTerm h (Int.le_of_lt this)
      (fun l hl _ hll ht => commitInDurable_of_complete h hi this hlc l hl hll ht)

/-- **`ReturnToFollowerState(i, m)`.** -/
theorem specInv_returnToFollowerState {σ σ' : State} {i : ID} {m : Etcdraft.Msg} (h : SpecInv σ)
    (hi : i ∈ σ.server) (hstep : σ.returnToFollowerState i m = some σ') : SpecInv σ' := by
  unfold State.returnToFollowerState at hstep; dsimp only at hstep
  split at hstep
  · cases hstep
  · cases hstep
    exact specInv_upd_follower h rfl (Int.le_refl _) rfl rfl rfl
      (fun l hl _ hll ht => h.commitInDurable i hi l hl hll ht.symm)

/-- **States that agree** as in `specInv_congr`, but for the votes granted, which may differ except
at an unpersisted candidate with none. -/
theorem specInv_congr_v {σ σ' : State} (h : SpecInv σ) (hsrv : σ'.server = σ.server)
    (hm : σ'.messages.domain = σ.messages.domain) (hp : σ'.pendingMessages.domain = σ.pendingMessages.domain)
    (hT : ∀ j, (σ'.s j).currentTerm = (σ.s j).currentTerm) (hS : ∀ j, (σ'.s j).state = (σ.s j).state)
    (hL : ∀ j, (σ'.s j).log = (σ.s j).log) (hD : ∀ j, (σ'.s j).durable = (σ.s j).durable)
    (hC : ∀ j, (σ'.s j).commitIndex = (σ.s j).commitIndex)
    (hM : ∀ j, (σ'.s j).matchIndex = (σ.s j).matchIndex)
    (hG : ∀ j, (σ'.s j).config = (σ.s j).config)
    (hV : ∀ j, (σ.s j).state = candidate → ¬ persisted (σ.s j) → (σ.s j).votesGranted = [] →
      (σ'.s j).votesGranted = []) : SpecInv σ' := by
  obtain ⟨hLE, hDu, hTm, hCa, hP, hCW, hRC, hRCC, hLDP, hLT, hCF⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, cfgFixed_congr hCF hsrv hG⟩
  · simp only [LeaderEntries, hsrv, hm, hp, hT, hS, hL]; exact hLE
  · simp only [DurS, hsrv, hm, hp, hT, hS, hL, hD, hC, hM]; exact hDu
  · simp only [TermsLe, MsgTermOk, msgs, hm, hp, hT]; exact hTm
  · intro l hl hc
    rw [hsrv] at hl; rw [hS] at hc
    obtain ⟨c1, c2, c3⟩ := hCa l hl hc
    simp only [msgs, persisted, hm, hp, hT, hL, hD]
    refine ⟨c1, c2, ?_⟩
    rcases c3 with hp' | ⟨v1, v2⟩
    · exact Or.inl hp'
    · by_cases hpp : persisted (σ.s l)
      · exact Or.inl hpp
      · exact Or.inr ⟨hV l hc hpp v1, v2⟩
  · simp only [PrevOk, msgs, hm, hp]; exact hP
  · simp only [CommitInDurable, hsrv, hS, hT, hC, hD]; exact hCW
  · simp only [ReqCommit, msgs, hsrv, hm, hp, hS, hT, hD]; exact hRC
  · simp only [ReqCommitC, msgs, hsrv, hm, hp, hC]; exact hRCC
  · simp only [LeaderDurPrefix, hsrv, hS, hT, hL, hD]; exact hLDP
  · simp only [LogTermsLe, msgs, hsrv, hm, hp, hT, hL]; exact hLT

/-- `MsgOk` reads only the servers' terms, roles, logs and durable states, and their commit indices,
which may rise. -/
theorem msgOk_congr {σ σ' : State} {m : Etcdraft.Msg} (h : MsgOk σ m) (hsrv : σ'.server = σ.server)
    (hT : ∀ j, (σ'.s j).currentTerm = (σ.s j).currentTerm) (hS : ∀ j, (σ'.s j).state = (σ.s j).state)
    (hL : ∀ j, (σ'.s j).log = (σ.s j).log) (hD : ∀ j, (σ'.s j).durable = (σ.s j).durable)
    (hC : ∀ j, (σ.s j).commitIndex ≤ (σ'.s j).commitIndex) :
    MsgOk σ' m := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  simp only [MsgOk, MsgTermOk, persisted, hsrv, hT, hS, hL, hD]
  exact ⟨h1, h2, h3, h4, h5, h6, fun hty => ⟨(h7 hty).1, Int.le_trans (h7 hty).2 (hC _)⟩⟩

/-- A vote response is fine to send when it is of its source's term, a granted one also of its
destination's, and a granted one of an unpersisted candidate's term is the candidate's own. -/
theorem msgOk_vote (σ : State) (r : Etcdraft.Msg) (he : r.entries = [])
    (hty : r.type = .requestVoteResponse) (ht : r.term ≤ (σ.s r.source).currentTerm)
    (hg : r.voteGranted = true → r.term ≤ (σ.s r.dest).currentTerm)
    (hc : ∀ l ∈ σ.server, (σ.s l).state = candidate → ¬ persisted (σ.s l) → r.dest = l →
      r.voteGranted = true → r.term = (σ.s l).currentTerm → r.source = l) : MsgOk σ r := by
  refine ⟨?_, ?_, ⟨ht, ?_⟩, ?_, ?_, ?_, fun h => ?_⟩
  · intro i _ _ k e hk; rw [he] at hk; simp at hk
  · intro i _ _
    refine ⟨fun _ h => ?_, fun _ h => ?_, fun h => ?_⟩ <;> rw [hty] at h <;> cases h
  · rintro (⟨_, h2⟩ | ⟨h1, _⟩)
    · exact hg h2
    · rw [hty] at h1; cases h1
  · intro i hi hc'
    refine ⟨fun _ h => ?_, fun _ h => ?_, fun hp hd _ hg' ht' => hc i hi hc' hp hd hg' ht'⟩ <;>
      rw [hty] at h <;> cases h
  · intro h; exact absurd he h
  · intro e h; rw [he] at h; cases h
  · rw [hty] at h; cases h

/-- **`RequestVote(i, j)`.** -/
theorem specInv_requestVote {σ σ' : State} {i j : ID} (h : SpecInv σ)
    (hstep : σ.requestVote i j = some σ') : SpecInv σ' := by
  unfold State.requestVote at hstep; dsimp only at hstep
  split at hstep
  · split at hstep
    · cases hstep
      exact specInv_send h (msgOk_plain _ _ rfl (by simp) (by simp) (by simp) (Int.le_refl _))
    · cases hstep
      exact specInv_send h (msgOk_vote _ _ rfl rfl (Int.le_refl _) (fun _ => Int.le_refl _)
        (fun _ _ _ _ hd _ _ => hd))
  · cases hstep

/-- **`AppendEntriesToSelf(i)`.** -/
theorem specInv_appendEntriesToSelf {σ σ' : State} {i : ID} (h : SpecInv σ)
    (hstep : σ.appendEntriesToSelf i = some σ') : SpecInv σ' := by
  unfold State.appendEntriesToSelf at hstep; dsimp only at hstep
  split at hstep
  · cases hstep
  · cases hstep
    rename_i hl
    have hl : (σ.s i).state = leader := by simpa using hl
    apply specInv_send h
    refine ⟨?_, ?_, ⟨Int.le_refl _, fun _ => Int.le_refl _⟩, ?_, ?_, fun e he => by simp at he,
      fun h => absurd h (by simp)⟩
    · intro l _ _ k e hk; simp at hk
    · intro l _ _
      refine ⟨fun _ h _ => absurd h (by simp), fun hd _ _ _ => ?_, fun h _ => absurd h (by simp)⟩
      dsimp only at hd; subst hd
      exact ⟨Int.le_refl _, fun hne => absurd rfl hne⟩
    · intro l _ hc
      refine ⟨fun _ h => absurd h (by simp), fun hd _ _ => ?_, fun _ _ h => absurd h (by simp)⟩
      dsimp only at hd; subst hd
      exact absurd (hc.symm.trans hl) candidate_ne_leader
    · intro h; exact absurd rfl h

/-- **`DropStaleResponse(i, j, m)`.** -/
theorem specInv_dropStaleResponse {σ σ' : State} {i j : ID} {m : Etcdraft.Msg} (h : SpecInv σ)
    (hstep : σ.dropStaleResponse i j m = some σ') : SpecInv σ' := by
  unfold State.dropStaleResponse at hstep
  split at hstep
  · cases hstep
  · cases hstep; exact specInv_discard m h

/-- **`HandleRequestVoteRequest(i, j, m)`**, `m` a request in `messages` from `j`. -/
theorem specInv_handleRequestVoteRequest {σ σ' : State} {i j : ID} {m : Etcdraft.Msg} (h : SpecInv σ)
    (hm : m ∈ σ.messages.domain) (hsrc : m.source = j)
    (hstep : σ.handleRequestVoteRequest i j m = some σ') : SpecInv σ' := by
  subst hsrc
  unfold State.handleRequestVoteRequest at hstep; dsimp only at hstep
  split at hstep
  · cases hstep
  · cases hstep
    -- the response, fine to send in `σ`
    have hok : ∀ g : Bool, (g = true → m.term = (σ.s i).currentTerm) →
        MsgOk σ
          { type := .requestVoteResponse, term := (σ.s i).currentTerm, voteGranted := g, source := i, dest := m.source } := by
      intro g hg
      apply msgOk_vote _ _ rfl rfl (Int.le_refl _)
      · intro hg'
        have := (h.2.2.1 m (List.mem_append_left _ hm)).1
        show (σ.s i).currentTerm ≤ (σ.s m.source).currentTerm
        rw [← hg hg']; exact this
      · intro l hl hc hp hd hg' ht
        change m.source = l at hd
        change (σ.s i).currentTerm = (σ.s l).currentTerm at ht
        change i = l
        subst hd
        by_cases hil : i = m.source
        · exact hil
        · exfalso
          rcases (h.2.2.2.1 m.source hl hc).2.2 with hp' | ⟨_, v2, -⟩
          · exact hp hp'
          · have := v2 m hm rfl
            rw [← ht, ← hg hg'] at this; exact Int.lt_irrefl _ this
    split
    · rename_i hg
      have hgt : m.term = (σ.s i).currentTerm := by
        simp only [Bool.and_eq_true, beq_iff_eq] at hg; exact hg.1.1
      apply specInv_reply
      · exact specInv_upd_frame h rfl rfl rfl rfl rfl rfl rfl rfl
      · exact msgOk_congr (hok _ (fun _ => hgt)) rfl
          (fun k => by by_cases hk : k = i <;> simp [State.discard, upd_s, hk])
          (fun k => by by_cases hk : k = i <;> simp [State.discard, upd_s, hk])
          (fun k => by by_cases hk : k = i <;> simp [State.discard, upd_s, hk])
          (fun k => by by_cases hk : k = i <;> simp [State.discard, upd_s, hk])
          (fun k => by by_cases hk : k = i <;> simp [State.discard, upd_s, hk])
    · rename_i hg
      apply specInv_reply h
      exact msgOk_congr (hok _ (fun h' => absurd h' hg)) rfl (fun _ => rfl) (fun _ => rfl)
        (fun _ => rfl) (fun _ => rfl) (fun _ => Int.le_refl _)

/-- **`HandleRequestVoteResponse(i, j, m)`**, `m` a vote response in `messages` to `i`. -/
theorem specInv_handleRequestVoteResponse {σ σ' : State} {i j : ID} {m : Etcdraft.Msg} (h : SpecInv σ)
    (hi : i ∈ σ.server) (hm : m ∈ σ.messages.domain) (hdst : m.dest = i)
    (hty : m.type = .requestVoteResponse) (hstep : σ.handleRequestVoteResponse i j m = some σ') :
    SpecInv σ' := by
  unfold State.handleRequestVoteResponse at hstep; dsimp only at hstep
  split at hstep
  · cases hstep
  · cases hstep
    rename_i hterm
    have hterm : m.term = (σ.s i).currentTerm := by simpa using hterm
    apply specInv_discard
    split
    · exact h
    · refine specInv_congr_v (σ' := σ.upd i _) h rfl rfl rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
      all_goals try (intro k; simp only [upd_s]; split <;> subst_vars <;> rfl)
      intro k hc hp hv
      simp only [upd_s]
      split
      · rename_i hki; subst hki
        split
        · rename_i hg
          exfalso
          rcases (h.2.2.2.1 _ hi hc).2.2 with hp' | ⟨_, _, v3, _⟩
          · exact hp hp'
          · have := v3 m hm hdst hty hg
            rw [hterm] at this; exact Int.lt_irrefl _ this
        · exact hv
      · exact hv

/-- **States that agree** as in `specInv_congr`, but for the match indices, which may differ when
a leader's stay within its durable log. -/
theorem specInv_congr_m {σ σ' : State} (h : SpecInv σ) (hsrv : σ'.server = σ.server)
    (hm : σ'.messages.domain = σ.messages.domain) (hp : σ'.pendingMessages.domain = σ.pendingMessages.domain)
    (hT : ∀ j, (σ'.s j).currentTerm = (σ.s j).currentTerm) (hS : ∀ j, (σ'.s j).state = (σ.s j).state)
    (hL : ∀ j, (σ'.s j).log = (σ.s j).log) (hD : ∀ j, (σ'.s j).durable = (σ.s j).durable)
    (hV : ∀ j, (σ'.s j).votesGranted = (σ.s j).votesGranted)
    (hC : ∀ j, (σ'.s j).commitIndex = (σ.s j).commitIndex)
    (hG : ∀ j, (σ'.s j).config = (σ.s j).config)
    (hM : ∀ j ∈ σ.server, (σ.s j).state = leader → ∀ k ∈ σ.server,
      (σ'.s j).matchIndex k ≤ (σ.s j).durable.log.length) : SpecInv σ' := by
  obtain ⟨hLE, hDu, hTm, hCa, hP, hCW, hRC, hRCC, hLDP, hLT, hCF⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, cfgFixed_congr hCF hsrv hG⟩
  · simp only [LeaderEntries, hsrv, hm, hp, hT, hS, hL]; exact hLE
  · intro l hl hll
    rw [hsrv] at hl; rw [hS] at hll
    obtain ⟨a1, a2, -, a4, a5, a6, a7⟩ := hDu l hl hll
    simp only [hm, hp, hT, hL, hD, hC]
    exact ⟨a1, a2, fun j hj => hM l hl hll j (by rwa [hsrv] at hj), a4, a5, a6, a7⟩
  · simp only [TermsLe, MsgTermOk, msgs, hm, hp, hT]; exact hTm
  · simp only [CandS, msgs, persisted, hsrv, hm, hp, hT, hS, hL, hD, hV]; exact hCa
  · simp only [PrevOk, msgs, hm, hp]; exact hP
  · simp only [CommitInDurable, hsrv, hS, hT, hC, hD]; exact hCW
  · simp only [ReqCommit, msgs, hsrv, hm, hp, hS, hT, hD]; exact hRC
  · simp only [ReqCommitC, msgs, hsrv, hm, hp, hC]; exact hRCC
  · simp only [LeaderDurPrefix, hsrv, hS, hT, hL, hD]; exact hLDP
  · simp only [LogTermsLe, msgs, hsrv, hm, hp, hT, hL]; exact hLT

/-- **`HandleAppendEntriesResponse(i, j, m)`**, `m` an append response in `messages` to `i`. -/
theorem specInv_handleAppendEntriesResponse {σ σ' : State} {i j : ID} {m : Etcdraft.Msg}
    (h : SpecInv σ) (hm : m ∈ σ.messages.domain) (hdst : m.dest = i)
    (hty : m.type = .appendEntriesResponse) (hstep : σ.handleAppendEntriesResponse i j m = some σ') :
    SpecInv σ' := by
  unfold State.handleAppendEntriesResponse at hstep; dsimp only at hstep
  split at hstep
  · cases hstep
  · cases hstep
    rename_i hterm
    have hterm : m.term = (σ.s i).currentTerm := by simpa using hterm
    apply specInv_discard
    split
    · rename_i hs
      refine specInv_congr_m (σ' := σ.upd i _) h rfl rfl rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
      all_goals try (intro k; by_cases hk : k = i <;> simp [upd_s, hk]; done)
      intro l hl hll k hk
      by_cases hli : l = i
      · subst hli
        obtain ⟨-, -, a3, -, -, a6, -⟩ := h.2.1 l hl hll
        rw [upd_s_self]
        dsimp only
        split
        · rename_i hkj; exact Int.max_le.mpr ⟨a3 _ (hkj ▸ hk), a6 m hm hdst hty hterm hs⟩
        · exact a3 k hk
      · rw [upd_s_ne _ _ _ _ hli]; exact (h.2.1 l hl hll).2.2.1 k hk
    · exact h

/-- **`ApplySimpleConfChange(i)` reapplying `i`'s configuration** (the case the simulation takes,
`TraceSimMatch`'s `AccIdle`: the last committed configuration entry is `i`'s configuration `(nc, lr)`;
`applySimpleConfChange_idle` gives this successor, as `accSrv`): the configuration and every other
field kept but `i`'s match indices, those outside `nc ∪ lr` zeroed. Only `DurS` reads them, and a zero
is within the durable log. -/
theorem specInv_applySimpleConfChange {σ : State} {i : ID} {nc lr : SetIds} (h : SpecInv σ) :
    SpecInv (σ.upd i (fun v => { v with matchIndex := fun j => if (nc.union lr).contains j then v.matchIndex j else 0 })) := by
  refine specInv_congr_m h rfl rfl rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  all_goals try (intro k; by_cases hk : k = i <;> simp [upd_s, hk]; done)
  intro l hl hll k hk
  have hm := (h.2.1 l hl hll).2.2.1 k hk
  by_cases hli : l = i
  · subst hli
    rw [upd_s_self]; dsimp only
    split
    · exact hm
    · exact Int.natCast_nonneg _
  · rw [upd_s_ne _ _ _ _ hli]; exact hm

/-- **`RejectAppendEntriesRequest(i, j, m, logOk)`** (no `PreVote`, no `CheckQuorum`: the rejection
is unsuccessful). -/
theorem specInv_rejectAppendEntriesRequest {σ σ' : State} {i j : ID} {m : Etcdraft.Msg} {logOk : Bool}
    (h : SpecInv σ) (hpv : σ.preVote = false) (hcq : σ.checkQuorum = false)
    (hstep : σ.rejectAppendEntriesRequest i j m logOk = some σ') : SpecInv σ' := by
  unfold State.rejectAppendEntriesRequest at hstep; dsimp only at hstep
  split at hstep
  · cases hstep
  · cases hstep
    exact specInv_reply h (msgOk_plain _ _ rfl (by simp) (fun _ => by simp [hpv, hcq]) (by simp)
      (Int.le_refl _))

/-- **`Timeout(i)`**; `hlc`: `LeaderComplete` at its new term (raft: leader completeness). -/
theorem specInv_timeout {σ σ' : State} {i : ID} (h : SpecInv σ) (hi : i ∈ σ.server)
    (hlc : LeaderComplete σ i ((σ.s i).currentTerm + 1))
    (hstep : σ.timeout i = some σ') : SpecInv σ' := by
  unfold State.timeout at hstep
  split at hstep
  · cases hstep
    have hTm := h.2.2.1
    have hsrc : ∀ m ∈ msgs σ, m.source = i → m.term ≤ (σ.s i).currentTerm := by
      intro m hm hs; have := (hTm m hm).1; rw [hs] at this; exact this
    have hdst : ∀ m ∈ msgs σ, m.dest = i → ((m.type = .requestVoteResponse ∧ m.voteGranted = true) ∨
        (m.type = .appendEntriesResponse ∧ m.success = true)) → m.term ≤ (σ.s i).currentTerm := by
      intro m hm hd hh; have := (hTm m hm).2 hh; rw [hd] at this; exact this
    apply specInv_upd_nonleader h (by simp only; exact candidate_ne_leader) (by simp only; omega) rfl rfl rfl
      (fun l hl _ hll ht => commitInDurable_of_complete h hi (by omega) hlc l hl hll ht)
    intro _
    simp only
    refine ⟨fun m hm hs _ => by have := hsrc m hm hs; omega,
      fun m hm hd ht hs => by have := hdst m hm hd (Or.inr ⟨ht, hs⟩); omega, ?_⟩
    by_cases hp : persisted (σ.s i)
    · exact Or.inl hp
    · refine Or.inr ⟨trivial, fun m hm hs => ?_, fun m hm hd ht hg => ?_, fun m hm hd ht hg htm => ?_⟩
      · have := hsrc m (List.mem_append_left _ hm) hs; omega
      · have := hdst m (List.mem_append_left _ hm) hd (Or.inl ⟨ht, hg⟩); omega
      · have := hdst m (List.mem_append_right _ hm) hd (Or.inl ⟨ht, hg⟩); omega
  · cases hstep

/-- **`Ready(i)`.** -/
theorem specInv_ready {σ : State} {i : ID} (h : SpecInv σ) : SpecInv (σ.ready i) := by
  obtain ⟨hLE, hD, hTm, hCa, hP, hCW, hRC, hRCC, hLDP, ⟨hLT1, hLT2⟩, hCF⟩ := h
  have hM : ∀ x ∈ (σ.ready i).messages.domain,
      x ∈ σ.messages.domain ∨ (x ∈ σ.pendingMessages.domain ∧ x.source = i) := by
    intro x hx
    simp only [State.ready] at hx
    rcases mem_plus _ _ x hx with hx | hx
    · obtain ⟨h1, h2⟩ := mem_filterMsgs _ _ x hx
      exact Or.inr ⟨h1, by simpa using h2⟩
    · exact Or.inl hx
  have hP' : ∀ x ∈ (σ.ready i).pendingMessages.domain, x ∈ σ.pendingMessages.domain := by
    intro x hx; simp only [State.ready] at hx; exact mem_minus _ _ x hx
  have hA : ∀ x ∈ msgs (σ.ready i), x ∈ msgs σ := by
    intro x hx; unfold msgs at hx ⊢
    rcases List.mem_append.mp hx with hx | hx
    · rcases hM x hx with hx | ⟨hx, -⟩
      · exact List.mem_append_left _ hx
      · exact List.mem_append_right _ hx
    · exact List.mem_append_right _ (hP' x hx)
  have hs : ∀ k, (σ.ready i).s k = if k = i then { σ.s i with durable := durableOf (σ.s i) } else σ.s k :=
    fun k => rfl
  have hsrv : (σ.ready i).server = σ.server := rfl
  -- every field but `i`'s durable state is kept
  have hT : ∀ k, ((σ.ready i).s k).currentTerm = (σ.s k).currentTerm := by
    intro k; rw [hs]; split <;> subst_vars <;> rfl
  have hS : ∀ k, ((σ.ready i).s k).state = (σ.s k).state := by
    intro k; rw [hs]; split <;> subst_vars <;> rfl
  have hL : ∀ k, ((σ.ready i).s k).log = (σ.s k).log := by
    intro k; rw [hs]; split <;> subst_vars <;> rfl
  have hC : ∀ k, ((σ.ready i).s k).commitIndex = (σ.s k).commitIndex := by
    intro k; rw [hs]; split <;> subst_vars <;> rfl
  have hMi : ∀ k, ((σ.ready i).s k).matchIndex = (σ.s k).matchIndex := by
    intro k; rw [hs]; split <;> subst_vars <;> rfl
  have hV : ∀ k, ((σ.ready i).s k).votesGranted = (σ.s k).votesGranted := by
    intro k; rw [hs]; split <;> subst_vars <;> rfl
  have hDi : ((σ.ready i).s i).durable.log = (σ.s i).log := by rw [hs]; simp [durableOf]
  have hDk : ∀ k, k ≠ i → ((σ.ready i).s k).durable = (σ.s k).durable := by
    intro k hk; rw [hs]; simp [hk]
  -- a leader's durable log only grows
  have hgrow : ∀ l ∈ σ.server, (σ.s l).state = leader →
      ((σ.s l).durable.log.length : Int) ≤ ((σ.ready i).s l).durable.log.length := by
    intro l hl hll
    by_cases hli : l = i
    · subst hli; rw [hDi]; exact (hD l hl hll).1
    · rw [hDk l hli]; exact Int.le_refl _
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ⟨?_, ?_⟩,
    cfgFixed_congr hCF hsrv (fun k => by rw [hs]; split <;> subst_vars <;> rfl)⟩
  · intro l hl hll
    rw [hsrv] at hl; rw [hS] at hll
    obtain ⟨h1, h2⟩ := hLE l hl hll
    simp only [hT, hL]
    exact ⟨fun j hj k e he ht => h1 j hj k e he ht,
      fun x hx => h2 x (hA x hx)⟩
  · intro l hl hll
    rw [hsrv] at hl; rw [hS] at hll
    obtain ⟨a1, a2, a3, a4, a5, a6, a7⟩ := hD l hl hll
    simp only [hT, hL, hC, hMi]
    by_cases hli : l = i
    · subst hli
      rw [hDi]
      refine ⟨Int.le_refl _, Int.le_trans a2 a1, fun k hk => Int.le_trans (a3 k hk) a1, ?_, ?_, ?_, ?_⟩
      · intro x hx hs' hty ht
        rcases hM x hx with hx | ⟨hx, -⟩
        · exact Int.le_trans (a4 x hx hs' hty ht) a1
        · exact a5 x hx hs' hty ht
      · intro x hx; exact a5 x (hP' x hx)
      · intro x hx hd hty ht hsc
        rcases hM x hx with hx | ⟨hx, -⟩
        · exact Int.le_trans (a6 x hx hd hty ht hsc) a1
        · exact (a7 x hx hd hty ht hsc).1
      · intro x hx hd hty ht hsc
        have := a7 x (hP' x hx) hd hty ht hsc
        exact ⟨this.1, fun _ => this.1⟩
    · rw [hDk l hli]
      refine ⟨a1, a2, a3, ?_, fun x hx => a5 x (hP' x hx), ?_, fun x hx => a7 x (hP' x hx)⟩
      · intro x hx hs' hty ht
        rcases hM x hx with hx | ⟨_, hsi⟩
        · exact a4 x hx hs' hty ht
        · exact absurd (hsi.symm.trans hs') (Ne.symm hli)
      · intro x hx hd hty ht hsc
        rcases hM x hx with hx | ⟨hx, hsi⟩
        · exact a6 x hx hd hty ht hsc
        · exact (a7 x hx hd hty ht hsc).2 (by rw [hsi]; exact Ne.symm hli)
  · intro x hx; unfold MsgTermOk; rw [hT, hT]; exact hTm x (hA x hx)
  · intro l hl hc
    rw [hsrv] at hl; rw [hS] at hc
    obtain ⟨c1, c2, c3⟩ := hCa l hl hc
    simp only [hT]
    refine ⟨fun x hx => c1 x (hA x hx), fun x hx => c2 x (hA x hx), ?_⟩
    by_cases hli : l = i
    · subst hli
      left; unfold persisted; rw [hDi, hL]
    · unfold persisted; rw [hDk l hli, hL, hV]
      rcases c3 with hp' | ⟨v1, v2, v3, v4⟩
      · exact Or.inl hp'
      · refine Or.inr ⟨v1, fun x hx hs' => ?_, fun x hx hd hty hg => ?_, fun x hx => v4 x (hP' x hx)⟩
        · rcases hM x hx with hx | ⟨_, hsi⟩
          · exact v2 x hx hs'
          · exact absurd (hsi.symm.trans hs') (Ne.symm hli)
        · rcases hM x hx with hx | ⟨hx, hsi⟩
          · exact v3 x hx hd hty hg
          · have hle := (hTm x (List.mem_append_right _ hx)).2 (Or.inl ⟨hty, hg⟩)
            rw [hd] at hle
            rcases Int.lt_or_eq_of_le hle with hlt | heq
            · exact hlt
            · exact absurd ((v4 x hx hd hty hg heq).symm.trans hsi) hli
  · intro x hx; exact hP x (hA x hx)
  · intro k hk l hl hll ht
    rw [hS] at hll; rw [hT, hT] at ht; rw [hC]
    exact Int.le_trans (hCW k hk l hl hll ht) (hgrow l hl hll)
  · intro l hl hll x hx hty ht
    rw [hS] at hll; rw [hT] at ht
    exact Int.le_trans (hRC l hl hll x (hA x hx) hty ht) (hgrow l hl hll)
  · intro x hx hty; rw [hC]; exact hRCC x (hA x hx) hty
  · intro l hl hll k e he ht
    rw [hS] at hll; rw [hT] at ht; rw [hL] at he
    exact Int.lt_of_lt_of_le (hLDP l hl hll k e he ht) (hgrow l hl hll)
  · intro k hk e he; rw [hT]; rw [hL] at he; exact hLT1 k hk e he
  · intro x hx; exact hLT2 x (hA x hx)

/-! ## The leader's actions -/

theorem getElem?_map_append {l r : List Entry} {k : Nat} {t : Int} (h : (l[k]?).map Entry.term = some t) :
    ((l ++ r)[k]?).map Entry.term = some t := by
  have hk : k < l.length := by
    rcases Nat.lt_or_ge k l.length with hk | hk
    · exact hk
    · rw [List.getElem?_eq_none hk] at h; cases h
  rw [List.getElem?_append_left hk]; exact h

/-- **`ClientRequest(i, v)`**: `i`'s new entry is the only one of its term elsewhere than in its log
(`MoreThanOneLeaderInv`). -/
theorem specInv_clientRequest {σ σ' : State} {i : ID} {val : Int} (h : SpecInv σ) (hi : i ∈ σ.server)
    (hone : σ.moreThanOneLeaderInv = true) (hstep : σ.clientRequest i val = some σ') : SpecInv σ' := by
  unfold State.clientRequest at hstep
  split at hstep
  · cases hstep
  · cases hstep
    rename_i hl
    have hil : (σ.s i).state = leader := by simpa using hl
    obtain ⟨hLE, hD, hTm, hCa, hP, hCW, hRC, hRCC, hLDP, ⟨hLT1, hLT2⟩, hCF⟩ := h
    have hs : ∀ k, (σ.replicate i (.val val) .value).s k = if k = i then
        { σ.s i with log := (σ.s i).log ++ [{ term := (σ.s i).currentTerm, type := .value, value := .val val }] }
        else σ.s k := fun k => rfl
    have hsrv : (σ.replicate i (.val val) .value).server = σ.server := rfl
    have hT : ∀ k, ((σ.replicate i (.val val) .value).s k).currentTerm = (σ.s k).currentTerm := by
      intro k; rw [hs]; split <;> subst_vars <;> rfl
    have hS : ∀ k, ((σ.replicate i (.val val) .value).s k).state = (σ.s k).state := by
      intro k; rw [hs]; split <;> subst_vars <;> rfl
    have hC : ∀ k, ((σ.replicate i (.val val) .value).s k).commitIndex = (σ.s k).commitIndex := by
      intro k; rw [hs]; split <;> subst_vars <;> rfl
    have hMi : ∀ k, ((σ.replicate i (.val val) .value).s k).matchIndex = (σ.s k).matchIndex := by
      intro k; rw [hs]; split <;> subst_vars <;> rfl
    have hDu : ∀ k, ((σ.replicate i (.val val) .value).s k).durable = (σ.s k).durable := by
      intro k; rw [hs]; split <;> subst_vars <;> rfl
    have hV : ∀ k, ((σ.replicate i (.val val) .value).s k).votesGranted = (σ.s k).votesGranted := by
      intro k; rw [hs]; split <;> subst_vars <;> rfl
    have hext : ∀ (k : ID) (n : Nat) (t : Int), ((σ.s k).log[n]?).map Entry.term = some t →
        (((σ.replicate i (.val val) .value).s k).log[n]?).map Entry.term = some t := by
      intro k n t ht; rw [hs]; split
      · subst_vars; exact getElem?_map_append ht
      · exact ht
    have hlen : ∀ k : ID, ((σ.s k).log.length : Int) ≤ ((σ.replicate i (.val val) .value).s k).log.length := by
      intro k; rw [hs]; split
      · subst_vars; simp only [List.length_append, List.length_singleton]; omega
      · exact Int.le_refl _
    have hcase : ∀ (k : ID) (n : Nat) (e : Entry), ((σ.replicate i (.val val) .value).s k).log[n]? = some e →
        (σ.s k).log[n]? = some e ∨ (k = i ∧ e.term = (σ.s i).currentTerm) := by
      intro k n e he; rw [hs] at he; split at he
      · subst_vars
        rw [List.getElem?_append] at he
        split at he
        · exact Or.inl he
        · right; refine ⟨rfl, ?_⟩
          cases hn : n - (σ.s k).log.length with
          | zero => rw [hn] at he; simp at he; rw [← he]
          | succ _ => rw [hn] at he; simp at he
      · exact Or.inl he
    refine ⟨?_, ?_, ?_, ?_, hP, ?_, ?_, ?_, ?_, ⟨?_, hLT2⟩,
      cfgFixed_congr hCF hsrv (fun k => by rw [hs]; split <;> subst_vars <;> rfl)⟩
    · intro l hl hll
      rw [hS] at hll
      obtain ⟨h1, h2⟩ := hLE l hl hll
      rw [hT]
      refine ⟨fun j hj n e he ht => ?_, fun x hx n e he ht => hext l _ _ (h2 x hx n e he ht)⟩
      rcases hcase j n e he with he' | ⟨rfl, hte⟩
      · exact hext l _ _ (h1 j hj n e he' ht)
      · have := oneLeader hone hl hj hll hil (ht.symm.trans hte)
        subst this
        rw [he]; rfl
    · intro l hl hll
      rw [hS] at hll
      obtain ⟨a1, a2, a3, a4, a5, a6, a7⟩ := hD l hl hll
      simp only [hT, hC, hMi, hDu]
      have hn := hlen l
      exact ⟨Int.le_trans a1 hn, a2, a3, a4, fun x hx hs' hty ht => Int.le_trans (a5 x hx hs' hty ht) hn, a6,
        fun x hx hd hty ht hsc => ⟨Int.le_trans (a7 x hx hd hty ht hsc).1 hn, (a7 x hx hd hty ht hsc).2⟩⟩
    · intro x hx; unfold MsgTermOk; rw [hT, hT]; exact hTm x hx
    · intro l hl hc
      rw [hS] at hc
      have hli : l ≠ i := by rintro rfl; exact candidate_ne_leader (hc.symm.trans hil)
      rw [hs]; simp only [hli, ↓reduceIte]
      exact hCa l hl hc
    · intro k hk l hl hll ht
      rw [hS] at hll; rw [hT, hT] at ht; rw [hC, hDu]
      exact hCW k hk l hl hll ht
    · intro l hl hll x hx hty ht
      rw [hS] at hll; rw [hT] at ht; rw [hDu]
      exact hRC l hl hll x hx hty ht
    · intro x hx hty; rw [hC]; exact hRCC x hx hty
    · intro l hl hll n e he ht
      rw [hS] at hll; rw [hT] at ht; rw [hDu]
      rcases hcase l n e he with he' | ⟨rfl, hte⟩
      · exact hLDP l hl hll n e he' ht
      · omega
    · intro k hk e he
      rw [hT]
      obtain ⟨n, hn, hne⟩ := List.mem_iff_getElem.mp he
      rcases hcase k n e (by rw [List.getElem?_eq_getElem hn, hne]) with he' | ⟨rfl, hte⟩
      · exact hLT1 k hk e (List.mem_of_getElem? he')
      · omega

/-- **A server's new commit index**, every other field kept: no lower, within its durable log if a
leader, and within the durable log of every leader of its term. -/
theorem specInv_upd_commit {σ : State} {i : ID} {f : Server → Server} (h : SpecInv σ)
    (hT : (f (σ.s i)).currentTerm = (σ.s i).currentTerm) (hS : (f (σ.s i)).state = (σ.s i).state)
    (hL : (f (σ.s i)).log = (σ.s i).log) (hD : (f (σ.s i)).durable = (σ.s i).durable)
    (hV : (f (σ.s i)).votesGranted = (σ.s i).votesGranted)
    (hM : (f (σ.s i)).matchIndex = (σ.s i).matchIndex)
    (hG : (f (σ.s i)).config = (σ.s i).config)
    (hge : (σ.s i).commitIndex ≤ (f (σ.s i)).commitIndex)
    (hcd : (σ.s i).state = leader → (f (σ.s i)).commitIndex ≤ (σ.s i).durable.log.length)
    (hcl : ∀ l ∈ σ.server, (σ.s l).state = leader → (σ.s l).currentTerm = (σ.s i).currentTerm →
      (f (σ.s i)).commitIndex ≤ (σ.s l).durable.log.length) : SpecInv (σ.upd i f) := by
  obtain ⟨hLE, hDu, hTm, hCa, hP, hCW, hRC, hRCC, hLDP, ⟨hLT1, hLT2⟩, hCF⟩ := h
  have hT' : ∀ k, ((σ.upd i f).s k).currentTerm = (σ.s k).currentTerm := by
    intro k; rw [upd_s]; split <;> subst_vars <;> first | rfl | exact hT
  have hS' : ∀ k, ((σ.upd i f).s k).state = (σ.s k).state := by
    intro k; rw [upd_s]; split <;> subst_vars <;> first | rfl | exact hS
  have hL' : ∀ k, ((σ.upd i f).s k).log = (σ.s k).log := by
    intro k; rw [upd_s]; split <;> subst_vars <;> first | rfl | exact hL
  have hD' : ∀ k, ((σ.upd i f).s k).durable = (σ.s k).durable := by
    intro k; rw [upd_s]; split <;> subst_vars <;> first | rfl | exact hD
  have hV' : ∀ k, ((σ.upd i f).s k).votesGranted = (σ.s k).votesGranted := by
    intro k; rw [upd_s]; split <;> subst_vars <;> first | rfl | exact hV
  have hM' : ∀ k, ((σ.upd i f).s k).matchIndex = (σ.s k).matchIndex := by
    intro k; rw [upd_s]; split <;> subst_vars <;> first | rfl | exact hM
  have hC' : ∀ k, (σ.s k).commitIndex ≤ ((σ.upd i f).s k).commitIndex := by
    intro k; rw [upd_s]; split <;> subst_vars <;> first | exact Int.le_refl _ | exact hge
  refine ⟨?_, ?_, ?_, ?_, hP, ?_, ?_, ?_, ?_, ⟨?_, hLT2⟩, cfgFixed_upd hCF hG⟩
  · simp only [LeaderEntries, hS', hT', hL']; exact hLE
  · intro l hl hll
    rw [hS'] at hll
    obtain ⟨a1, a2, a3, a4, a5, a6, a7⟩ := hDu l hl hll
    simp only [hT', hL', hD', hM']
    refine ⟨a1, ?_, a3, a4, a5, a6, a7⟩
    by_cases hli : l = i
    · subst hli; rw [upd_s_self]; exact hcd hll
    · rw [upd_s_ne _ _ _ _ hli]; exact a2
  · simp only [TermsLe, MsgTermOk, hT']; exact hTm
  · simp only [CandS, persisted, hS', hT', hL', hD', hV']; exact hCa
  · intro k hk l hl hll ht
    rw [hS'] at hll; rw [hT', hT'] at ht; rw [hD']
    by_cases hki : k = i
    · subst hki; rw [upd_s_self]; exact hcl l hl hll ht.symm
    · rw [upd_s_ne _ _ _ _ hki]; exact hCW k hk l hl hll ht
  · simp only [ReqCommit, hS', hT', hD']; exact hRC
  · intro x hx hty; exact ⟨(hRCC x hx hty).1, Int.le_trans (hRCC x hx hty).2 (hC' _)⟩
  · simp only [LeaderDurPrefix, hS', hT', hL', hD']; exact hLDP
  · simp only [hT', hL']; exact hLT1

theorem foldl_last (Q : Nat → Bool) (N : Nat) :
    (List.range N).foldl (fun (acc : Nat) n => if Q n = true then n + 1 else acc) 0 = 0 ∨
    ∃ n, (List.range N).foldl (fun (acc : Nat) n => if Q n = true then n + 1 else acc) 0 = n + 1 ∧
      n < N ∧ Q n = true := by
  induction N with
  | zero => left; rfl
  | succ N ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    split
    · rename_i hq; right; exact ⟨N, rfl, Nat.lt_succ_self _, hq⟩
    · rcases ih with h0 | ⟨n, h1, h2, h3⟩
      · left; exact h0
      · right; exact ⟨n, h1, Nat.lt_succ_of_lt h2, h3⟩

theorem isQuorum_nonempty {q c : SetIds} (h : isQuorum q c = true) : ∃ k, k ∈ q := by
  unfold isQuorum at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  cases q with
  | nil => simp at h
  | cons k _ => exact ⟨k, List.mem_cons_self⟩

/-- **`AdvanceCommitIndex(i)`**: the new commit index is agreed by a quorum (so within the match
indices, within the durable log) and within the log. -/
theorem specInv_advanceCommitIndex {σ σ' : State} {i : ID} (h : SpecInv σ) (hi : i ∈ σ.server)
    (hone : σ.moreThanOneLeaderInv = true)
    (hstep : σ.advanceCommitIndex i = some σ') : SpecInv σ' := by
  -- (review round 2's A8) the configuration's members are servers (`CfgFixed`)
  have hcfg : ∀ k ∈ σ.getConfig i, k ∈ σ.server := by
    intro k hk; simp only [State.getConfig, h.cfgFixed i hi] at hk; exact hk
  unfold State.advanceCommitIndex at hstep; dsimp only at hstep
  split at hstep
  · cases hstep
  · cases hstep
    rename_i hl
    have hl : (σ.s i).state = leader := by simpa using hl
    obtain ⟨-, a2, a3, -⟩ := h.2.1 i hi hl
    have hcw := h.commitWithinLeader i hi i hi hl rfl
    -- the new commit index: within the durable log and the log
    have hnew : ∀ c : Int, (c ≤ (σ.s i).durable.log.length ∧ c ≤ (σ.s i).log.length) →
        max (σ.s i).commitIndex c ≤ (σ.s i).durable.log.length ∧
        max (σ.s i).commitIndex c ≤ (σ.s i).log.length := fun c hc =>
      ⟨Int.max_le.mpr ⟨a2, hc.1⟩, Int.max_le.mpr ⟨hcw, hc.2⟩⟩
    have hb := hnew
      (if (decide ((List.range (σ.s i).log.length).foldl (fun (acc : Nat) n =>
            if isQuorum ((σ.getConfig i).filter (fun k => decide ((σ.s i).matchIndex k ≥ ((n + 1 : Nat) : Int))))
              (σ.getConfig i) = true then n + 1 else acc) 0 > 0) &&
          (((σ.s i).log[(List.range (σ.s i).log.length).foldl (fun (acc : Nat) n =>
            if isQuorum ((σ.getConfig i).filter (fun k => decide ((σ.s i).matchIndex k ≥ ((n + 1 : Nat) : Int))))
              (σ.getConfig i) = true then n + 1 else acc) 0 - 1]?).map Entry.term == some (σ.s i).currentTerm)) = true
        then (((List.range (σ.s i).log.length).foldl (fun (acc : Nat) n =>
            if isQuorum ((σ.getConfig i).filter (fun k => decide ((σ.s i).matchIndex k ≥ ((n + 1 : Nat) : Int))))
              (σ.getConfig i) = true then n + 1 else acc) 0 : Nat) : Int)
        else (σ.s i).commitIndex) (by
        split
        · rcases foldl_last (fun n => isQuorum ((σ.getConfig i).filter
              (fun k => decide ((σ.s i).matchIndex k ≥ ((n + 1 : Nat) : Int))))
              (σ.getConfig i)) (σ.s i).log.length with h0 | ⟨n, h1, h2, h3⟩
          · rw [h0]; constructor <;> omega
          · rw [h1]
            obtain ⟨k, hk0⟩ := isQuorum_nonempty h3
            have hk := (List.mem_filter.mp hk0).2
            simp only [decide_eq_true_eq] at hk
            have := a3 k (hcfg k (List.mem_filter.mp hk0).1)
            constructor <;> omega
        · exact ⟨a2, hcw⟩)
    apply specInv_upd_commit h rfl rfl rfl rfl rfl rfl rfl (Int.le_max_left _ _)
    · intro _; exact hb.1
    · intro l hl' hll ht
      have := oneLeader hone hl' hi hll hl ht
      subst this
      exact hb.1

/-- **`BecomeLeader(i)`**, `i` of term `T`. What the specification's state does not record, and the
simulation supplies from raft's ghost state (raft's leader of a term is unique over time, and only it
creates entries and append requests of its term):

- `hfreshLog`, `hfreshMsg`: no entry of term `T` exists yet, in any log or any message;
- `hfreshReq`: no append request of term `T` exists yet;
- `hcw`: every server of term `T` has its commit index within `i`'s log (raft: leader completeness,
  the committed entries are in the new leader's log; for `i` itself, `CommitOk`).

The candidate's own facts (it has persisted its log, since a vote was granted; it has no append
request or successful response of its term) are `CandS`'s. -/
theorem specInv_becomeLeader {σ σ' : State} {i : ID} (h : SpecInv σ) (hi : i ∈ σ.server)
    (hfreshLog : ∀ j ∈ σ.server, ∀ e ∈ (σ.s j).log, e.term ≠ (σ.s i).currentTerm)
    (hfreshMsg : ∀ m ∈ msgs σ, ∀ e ∈ m.entries, e.term ≠ (σ.s i).currentTerm)
    (hfreshReq : ∀ m ∈ msgs σ, m.type = .appendEntriesRequest → m.term ≠ (σ.s i).currentTerm)
    (hcw : ∀ k ∈ σ.server, (σ.s k).currentTerm = (σ.s i).currentTerm →
      (σ.s k).commitIndex ≤ (σ.s i).log.length)
    (hstep : σ.becomeLeader i = some σ') : SpecInv σ' := by
  unfold State.becomeLeader at hstep; dsimp only at hstep
  split at hstep
  · cases hstep
    rename_i hc
    simp only [Bool.and_eq_true, beq_iff_eq] at hc
    obtain ⟨hcand, hq⟩ := hc
    obtain ⟨hLE, hD, hTm, hCa, hP, hCW, hRC, hRCC, hLDP, ⟨hLT1, hLT2⟩, hCF⟩ := h
    obtain ⟨c1, c2, c3⟩ := hCa i hi hcand
    have hpers : ((σ.s i).durable.log.length : Int) = (σ.s i).log.length := by
      rcases c3 with hp | ⟨hv, -⟩
      · unfold persisted at hp; rw [hp]
      · obtain ⟨k, hk⟩ := isQuorum_nonempty hq
        rw [hv] at hk; cases hk
    generalize hσ' : σ.upd i _ = σ'
    have hs : ∀ k, σ'.s k =
        if k = i then { σ.s i with state := leader, lead := i, matchIndex := fun j => if j = i then ((σ.s i).log.length : Int) else 0 }
        else σ.s k := by
      intro k; rw [← hσ']; rfl
    have hsrv : σ'.server = σ.server := by rw [← hσ']; rfl
    have hmsg : msgs σ' = msgs σ := by rw [← hσ']; rfl
    have hm : σ'.messages = σ.messages := by rw [← hσ']; rfl
    have hpm : σ'.pendingMessages = σ.pendingMessages := by rw [← hσ']; rfl
    have hT : ∀ k, (σ'.s k).currentTerm = (σ.s k).currentTerm := by
      intro k; rw [hs]; split <;> subst_vars <;> rfl
    have hL : ∀ k, (σ'.s k).log = (σ.s k).log := by
      intro k; rw [hs]; split <;> subst_vars <;> rfl
    have hC : ∀ k, (σ'.s k).commitIndex = (σ.s k).commitIndex := by
      intro k; rw [hs]; split <;> subst_vars <;> rfl
    have hne : ∀ k, k ≠ i → σ'.s k = σ.s k := by
      intro k hk; rw [hs]; simp [hk]
    have hsi : (σ'.s i).state = leader := by rw [hs]; simp
    have hDu : ∀ k, (σ'.s k).durable = (σ.s k).durable := by
      intro k; rw [hs]; split <;> subst_vars <;> rfl
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ⟨?_, ?_⟩,
      cfgFixed_congr hCF hsrv (fun k => by rw [hs]; split <;> subst_vars <;> rfl)⟩
    · intro l hl hll
      rw [hsrv] at hl
      by_cases hli : l = i
      · subst hli
        rw [hT]
        refine ⟨fun j hj k e he ht => ?_, fun x hx k e he ht => ?_⟩
        · rw [hsrv] at hj; rw [hL] at he
          exact absurd ht (hfreshLog j hj e (List.mem_of_getElem? he))
        · exact absurd ht (hfreshMsg x (hmsg ▸ hx) e (List.mem_of_getElem? he))
      · rw [hne l hli] at hll ⊢
        obtain ⟨h1, h2⟩ := hLE l hl hll
        refine ⟨fun j hj k e he ht => h1 j (hsrv ▸ hj) k e (by rw [← hL j]; exact he) ht,
          fun x hx => h2 x (by rw [← hm, ← hpm]; exact hx)⟩
    · intro l hl hll
      by_cases hli : l = i
      · subst hli
        rw [hm, hpm, hT, hL]
        have hd : (σ'.s l).durable = (σ.s l).durable := by rw [hs]; simp
        rw [hd, hC, hpers]
        refine ⟨Int.le_refl _, hcw l (hsrv ▸ hl) rfl, fun k _ => ?_, ?_, ?_, ?_, ?_⟩
        · rw [hs]; simp only [↓reduceIte]; split <;> omega
        · intro x hx hs' hty ht; have := c1 x (List.mem_append_left _ hx) hs' hty; omega
        · intro x hx hs' hty ht; have := c1 x (List.mem_append_right _ hx) hs' hty; omega
        · intro x hx hd' hty ht hsc; have := c2 x (List.mem_append_left _ hx) hd' hty hsc; omega
        · intro x hx hd' hty ht hsc; have := c2 x (List.mem_append_right _ hx) hd' hty hsc; omega
      · rw [hne l hli] at hll ⊢
        rw [hm, hpm]
        simpa [hsrv] using hD l (hsrv ▸ hl) hll
    · intro x hx; unfold MsgTermOk; rw [hT, hT]; exact hTm x (hmsg ▸ hx)
    · intro l hl hc
      have hli : l ≠ i := by rintro rfl; rw [hsi] at hc; exact candidate_ne_leader hc.symm
      rw [hne l hli] at hc ⊢
      rw [hmsg, hm, hpm]
      exact hCa l (hsrv ▸ hl) hc
    · intro x hx; exact hP x (hmsg ▸ hx)
    · intro k hk l hl hll ht
      rw [hT, hT] at ht; rw [hC, hDu]
      by_cases hli : l = i
      · subst hli; rw [hpers]; exact hcw k (hsrv ▸ hk) ht
      · rw [hne l hli] at hll; exact hCW k (hsrv ▸ hk) l (hsrv ▸ hl) hll ht
    · intro l hl hll x hx hty ht
      rw [hT] at ht; rw [hDu]
      by_cases hli : l = i
      · subst hli; exact absurd ht (hfreshReq x (hmsg ▸ hx) hty)
      · rw [hne l hli] at hll; exact hRC l (hsrv ▸ hl) hll x (hmsg ▸ hx) hty ht
    · intro x hx hty; rw [hsrv, hC]; exact hRCC x (hmsg ▸ hx) hty
    · intro l hl hll k e he ht
      rw [hT] at ht; rw [hL] at he; rw [hDu]
      by_cases hli : l = i
      · subst hli; rw [hpers]
        have := (List.getElem?_eq_some_iff.mp he).1
        omega
      · rw [hne l hli] at hll; exact hLDP l (hsrv ▸ hl) hll k e he ht
    · intro k hk e he; rw [hT]; rw [hL] at he; exact hLT1 k (hsrv ▸ hk) e he
    · intro x hx; exact hLT2 x (hmsg ▸ hx)
  · cases hstep

/-! ## Append requests -/

theorem subSeq_get {s l : List Entry} {m n : Int} (h : subSeq s m n = some l) {k : Nat} {e : Entry}
    (hk : l[k]? = some e) : 1 ≤ m ∧ s[(m.toNat - 1) + k]? = some e := by
  unfold subSeq at h
  split at h
  · cases h; simp at hk
  · split at h
    · cases h
    · cases h
      rename_i h1 h2
      refine ⟨by omega, ?_⟩
      rw [List.getElem?_take] at hk
      split at hk
      · rw [List.getElem?_drop] at hk; exact hk
      · cases hk

theorem subSeq_len {s l : List Entry} {m n : Int} (h : subSeq s m n = some l) :
    (n < m ∧ l = []) ∨ (1 ≤ m ∧ m ≤ n ∧ n ≤ s.length ∧ (l.length : Int) = n - m + 1) := by
  unfold subSeq at h
  split at h
  · cases h; left; constructor <;> first | omega | rfl
  · split at h
    · cases h
    · cases h
      rename_i h1 h2
      right
      refine ⟨by omega, by omega, by omega, ?_⟩
      simp only [List.length_take, List.length_drop]
      omega

/-- **`AppendEntriesInRangeToPeer(subtype, i, j, <<b, e>>)`**, `b` within `NextAsync`'s range
(`hb`: `b ≤ Len(log[i]) + 1`; past it, an empty request's `prevLogIndex` is past the leader's log and
a follower that has the entries of an older term acknowledges them: then `DurInv`, and
`CommittedIsDurableInv`, fail). -/
theorem specInv_appendEntriesInRangeToPeer {σ σ' : State} {subtype : String} {i j : ID} {b e : Int}
    (h : SpecInv σ) (hi : i ∈ σ.server) (hone : σ.moreThanOneLeaderInv = true)
    (hb : b ≤ (σ.s i).log.length + 1)
    (hstep : σ.appendEntriesInRangeToPeer subtype i j b e = .ok (some σ')) : SpecInv σ' := by
  unfold State.appendEntriesInRangeToPeer at hstep; dsimp only at hstep
  split at hstep
  · cases hstep
  · rename_i hc
    cases hsub : subSeq (σ.s i).log b (min ((σ.s i).log.length : Int) (e - 1)) with
    | none => simp [subSeqM, hsub, throw, throwThe, MonadExceptOf.throw, Functor.map, Except.map] at hstep
    | some ents =>
      simp [subSeqM, hsub] at hstep
      simp only [pure, Except.pure, Except.ok.injEq, Option.some.injEq] at hstep
      subst hstep
      have hl : (σ.s i).state = leader :=
        Classical.byContradiction fun hn => hc (by simp [hn])
      have hcw := (h.2.1 i hi hl).2.1
      have hlen := subSeq_len hsub
      -- the request's commit index, at most `i`'s
      have hcom : (if subtype = "heartbeat" then min (σ.s i).commitIndex ((σ.s i).matchIndex j)
          else if subtype = "snapshot" then min (σ.s i).commitIndex (min ((σ.s i).log.length : Int) (e - 1))
          else (σ.s i).commitIndex) ≤ (σ.s i).commitIndex := by
        (repeat' split) <;> omega
      apply specInv_send h
      refine ⟨?_, ?_, ⟨Int.le_refl _, ?_⟩, ?_, ?_, ?_, fun _ => ⟨hi, ?_⟩⟩
      · intro l hl' hll k x hk ht
        obtain ⟨hb1, hx⟩ := subSeq_get hsub hk
        have : (b - 1).toNat = b.toNat - 1 := by omega
        show ((σ.s l).log[((b - 1).toNat + k)]?).map Entry.term = some x.term
        rw [this]
        exact (h.1 l hl' hll).1 i hi _ x hx ht
      · intro l hl' hll
        refine ⟨fun hs _ _ => ?_, fun _ hty => absurd hty (by simp), fun _ ht => ?_⟩
        · change i = l at hs; subst hs
          show b - 1 + (ents.length : Int) ≤ (σ.s i).log.length
          rcases hlen with ⟨_, rfl⟩ | ⟨_, _, _, hn⟩
          · simp only [List.length_nil]; omega
          · omega
        · change (σ.s i).currentTerm = (σ.s l).currentTerm at ht
          have := oneLeader hone hi hl' hl hll ht
          subst this
          exact Int.le_trans (by simpa using hcom) hcw
      · rintro (⟨hty, _⟩ | ⟨hty, _⟩) <;> exact absurd hty (by simp)
      · intro l _ hc'
        refine ⟨fun hs _ => ?_, fun _ hty => absurd hty (by simp), fun _ _ hty => absurd hty (by simp)⟩
        change i = l at hs; subst hs
        exact absurd (hc'.symm.trans hl) candidate_ne_leader
      · intro hne
        show 0 ≤ b - 1
        rcases hlen with ⟨_, hn⟩ | ⟨_, _, _, _⟩
        · exact absurd hn hne
        · omega
      · intro x hx
        obtain ⟨k, hk, hkx⟩ := List.mem_iff_getElem.mp hx
        obtain ⟨-, hx'⟩ := subSeq_get hsub (by rw [List.getElem?_eq_getElem hk, hkx])
        exact h.logTermsLe.1 i hi x (List.mem_of_getElem? hx')
      · simpa using hcom

/-- **`AppendEntries(i, j, <<b, e>>)`**, `b` within `NextAsync`'s range. -/
theorem specInv_appendEntries {σ σ' : State} {i j : ID} {b e : Int}
    (h : SpecInv σ) (hi : i ∈ σ.server) (hone : σ.moreThanOneLeaderInv = true)
    (hb : b ≤ (σ.s i).log.length + 1)
    (hstep : σ.appendEntries i j b e = .ok (some σ')) : SpecInv σ' :=
  specInv_appendEntriesInRangeToPeer h hi hone hb hstep

/-- **`Heartbeat(i, j)`.** -/
theorem specInv_heartbeat {σ σ' : State} {i j : ID}
    (h : SpecInv σ) (hi : i ∈ σ.server) (hone : σ.moreThanOneLeaderInv = true)
    (hstep : σ.heartbeat i j = .ok (some σ')) : SpecInv σ' :=
  specInv_appendEntriesInRangeToPeer h hi hone (by omega) hstep

/-! ## A follower's handling of an append request -/

/-- **A follower's new log**, every other field kept: each entry of it of a leader's term at a
position where that leader's log has an entry of the term. -/
theorem specInv_upd_followerLog {σ : State} {i : ID} {f : Server → Server} (h : SpecInv σ)
    (hfol : (σ.s i).state = follower)
    (hT : (f (σ.s i)).currentTerm = (σ.s i).currentTerm) (hS : (f (σ.s i)).state = (σ.s i).state)
    (hD : (f (σ.s i)).durable = (σ.s i).durable)
    (hV : (f (σ.s i)).votesGranted = (σ.s i).votesGranted)
    (hC : (f (σ.s i)).commitIndex = (σ.s i).commitIndex)
    (hM : (f (σ.s i)).matchIndex = (σ.s i).matchIndex)
    (hG : (f (σ.s i)).config = (σ.s i).config)
    (hlog : ∀ (k : Nat) (e : Entry), (f (σ.s i)).log[k]? = some e → ∀ l ∈ σ.server, (σ.s l).state = leader →
      e.term = (σ.s l).currentTerm → ((σ.s l).log[k]?).map Entry.term = some e.term)
    (hlt : ∀ e ∈ (f (σ.s i)).log, e.term ≤ (σ.s i).currentTerm) :
    SpecInv (σ.upd i f) := by
  obtain ⟨hLE, hDu, hTm, hCa, hP, hCW, hRC, hRCC, hLDP, ⟨hLT1, hLT2⟩, hCF⟩ := h
  have hT' : ∀ k, ((σ.upd i f).s k).currentTerm = (σ.s k).currentTerm := by
    intro k; rw [upd_s]; split <;> subst_vars <;> first | rfl | exact hT
  have hS' : ∀ k, ((σ.upd i f).s k).state = (σ.s k).state := by
    intro k; rw [upd_s]; split <;> subst_vars <;> first | rfl | exact hS
  have hC' : ∀ k, ((σ.upd i f).s k).commitIndex = (σ.s k).commitIndex := by
    intro k; rw [upd_s]; split <;> subst_vars <;> first | rfl | exact hC
  -- the leaders and the candidates are not `i`
  have hnl : ∀ l, (σ.s l).state = leader → l ≠ i := by
    rintro l hl rfl; exact follower_ne_leader (hfol.symm.trans hl)
  have hnc : ∀ l, (σ.s l).state = candidate → l ≠ i := by
    rintro l hl rfl; exact follower_ne_candidate (hfol.symm.trans hl)
  refine ⟨?_, ?_, ?_, ?_, hP, ?_, ?_, ?_, ?_, ⟨?_, hLT2⟩, cfgFixed_upd hCF hG⟩
  · intro l hl hll
    rw [hS'] at hll
    rw [upd_s_ne _ _ _ _ (hnl l hll)]
    obtain ⟨h1, h2⟩ := hLE l hl hll
    refine ⟨fun j hj k e he ht => ?_, h2⟩
    by_cases hji : j = i
    · subst hji; rw [upd_s_self] at he; exact hlog k e he l hl hll ht
    · rw [upd_s_ne _ _ _ _ hji] at he; exact h1 j hj k e he ht
  · intro l hl hll
    rw [hS'] at hll
    rw [upd_s_ne _ _ _ _ (hnl l hll)]
    exact hDu l hl hll
  · simp only [TermsLe, MsgTermOk, hT']; exact hTm
  · intro l hl hc
    rw [hS'] at hc
    rw [upd_s_ne _ _ _ _ (hnc l hc)]
    exact hCa l hl hc
  · intro k hk l hl hll ht
    rw [hS'] at hll; rw [hT', hT'] at ht; rw [hC', upd_s_ne _ _ _ _ (hnl l hll)]
    exact hCW k hk l hl hll ht
  · intro l hl hll
    rw [hS'] at hll
    rw [upd_s_ne _ _ _ _ (hnl l hll)]
    exact hRC l hl hll
  · intro x hx hty; rw [hC']; exact hRCC x hx hty
  · intro l hl hll
    rw [hS'] at hll
    rw [upd_s_ne _ _ _ _ (hnl l hll)]
    exact hLDP l hl hll
  · intro k hk e he
    by_cases hki : k = i
    · subst hki; rw [upd_s_self] at he ⊢; rw [hT]; exact hlt e he
    · rw [upd_s_ne _ _ _ _ hki] at he ⊢; exact hLT1 k hk e he

/-- **`ConflictAppendEntriesRequest(i, index, m)`**, `i` a follower: its log loses its last entry. -/
theorem specInv_conflictAppendEntriesRequest {σ σ' : State} {i : ID} {index : Int} {m : Etcdraft.Msg}
    (h : SpecInv σ) (hi : i ∈ σ.server) (hfol : (σ.s i).state = follower)
    (hstep : σ.conflictAppendEntriesRequest i index m = .ok (some σ')) : SpecInv σ' := by
  unfold State.conflictAppendEntriesRequest at hstep; dsimp only at hstep
  split at hstep
  · cases hstep
  · cases hsub : subSeq (σ.s i).log 1 ((σ.s i).log.length - 1) with
    | none => simp [subSeqM, hsub, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at hstep
    | some ents =>
      simp [subSeqM, hsub] at hstep
      simp only [pure, Except.pure, Except.ok.injEq, Option.some.injEq] at hstep
      subst hstep
      apply specInv_upd_followerLog h hfol rfl rfl rfl rfl rfl rfl rfl
      · intro k e he l hl hll ht
        obtain ⟨-, hx⟩ := subSeq_get hsub he
        simp only [Int.toNat_one, Nat.sub_self, Nat.zero_add] at hx
        exact (h.1 l hl hll).1 i hi k e hx ht
      · intro e he
        obtain ⟨k, hk, hke⟩ := List.mem_iff_getElem.mp he
        obtain ⟨-, hx⟩ := subSeq_get hsub (by rw [List.getElem?_eq_getElem hk, hke])
        exact h.logTermsLe.1 i hi e (List.mem_of_getElem? hx)

/-- **`NoConflictAppendEntriesRequest(i, index, m)`**, `i` a follower, `m` an append request in either
bag of `i`'s term, `index` its `prevLogIndex + 1`: the new entries are `m`'s, at their positions. -/
theorem specInv_noConflictAppendEntriesRequest {σ σ' : State} {i : ID} {index : Int} {m : Etcdraft.Msg}
    (h : SpecInv σ) (hi : i ∈ σ.server) (hfol : (σ.s i).state = follower) (hm : m ∈ msgs σ)
    (hterm : m.term = (σ.s i).currentTerm) (hidx : index = m.prevLogIndex + 1)
    (hstep : σ.noConflictAppendEntriesRequest i index m = .ok (some σ')) : SpecInv σ' := by
  unfold State.noConflictAppendEntriesRequest at hstep; dsimp only at hstep
  split at hstep
  · cases hstep
  · rename_i hc
    have hne : m.entries ≠ [] := by
      intro he; apply hc; simp [he]
    have hp0 := h.2.2.2.2.1 m hm hne
    cases hsub : subSeq m.entries ((σ.s i).log.length - index + 2) m.entries.length with
    | none => simp [subSeqM, hsub, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at hstep
    | some suf =>
      simp [subSeqM, hsub] at hstep
      simp only [pure, Except.pure, Except.ok.injEq, Option.some.injEq] at hstep
      subst hstep
      apply specInv_upd_followerLog h hfol rfl rfl rfl rfl rfl rfl rfl
      · intro k e he l hl hll ht
        dsimp only at he
        rw [List.getElem?_append] at he
        split at he
        · exact (h.1 l hl hll).1 i hi k e he ht
        · rename_i hk
          obtain ⟨h1, hx⟩ := subSeq_get hsub he
          have hpos : m.prevLogIndex.toNat +
              ((((σ.s i).log.length : Int) - index + 2).toNat - 1 + (k - (σ.s i).log.length)) = k := by
            omega
          have := (h.1 l hl hll).2 m hm _ e hx ht
          rw [hpos] at this
          exact this
      · intro e he
        dsimp only at he
        rcases List.mem_append.mp he with he | he
        · exact h.logTermsLe.1 i hi e he
        · obtain ⟨k, hk, hke⟩ := List.mem_iff_getElem.mp he
          obtain ⟨-, hx⟩ := subSeq_get hsub (by rw [List.getElem?_eq_getElem hk, hke])
          rw [← hterm]; exact h.logTermsLe.2 m hm e (List.mem_of_getElem? hx)



theorem commitTo_fields (σ : State) (i : ID) (c : Int) (k : ID) :
    ((σ.commitTo i c).s k).currentTerm = (σ.s k).currentTerm ∧ ((σ.commitTo i c).s k).state = (σ.s k).state ∧
    ((σ.commitTo i c).s k).log = (σ.s k).log ∧ ((σ.commitTo i c).s k).durable = (σ.s k).durable ∧
    (σ.s k).commitIndex ≤ ((σ.commitTo i c).s k).commitIndex := by
  by_cases hk : k = i <;> simp [State.commitTo, upd_s, hk]
  subst hk; exact Int.le_max_left _ _

/-- A follower's commit index raised to a value within the durable log of every leader of its term. -/
theorem specInv_commitTo_follower {σ : State} {i : ID} {c : Int} (h : SpecInv σ) (hi : i ∈ σ.server)
    (hfol : (σ.s i).state = follower)
    (hc : ∀ l ∈ σ.server, (σ.s l).state = leader → (σ.s l).currentTerm = (σ.s i).currentTerm →
      c ≤ (σ.s l).durable.log.length) : SpecInv (σ.commitTo i c) := by
  apply specInv_upd_commit h rfl rfl rfl rfl rfl rfl rfl (Int.le_max_left _ _)
  · intro hl; exact absurd (hfol.symm.trans hl) follower_ne_leader
  · intro l hl hll ht
    exact Int.max_le.mpr ⟨h.commitInDurable i hi l hl hll ht.symm, hc l hl hll ht⟩

/-- **`AppendEntriesAlreadyDone(i, j, index, m)`**, under `AcceptAppendEntriesRequest`'s guard (`i` a
follower of `m`'s term), `m` an append request in `messages` from `j`, `index` its
`prevLogIndex + 1`. An acknowledgement of `i`'s commit index is within the durable log of `m`'s
sender when that leads `m`'s term, by `CommitInDurable` (review round 3's B6(b): no hypothesis). -/
theorem specInv_appendEntriesAlreadyDone {σ σ' : State} {i j : ID} {index : Int} {m : Etcdraft.Msg}
    (h : SpecInv σ) (hi : i ∈ σ.server) (hm : m ∈ σ.messages.domain) (hsrc : m.source = j)
    (hty : m.type = .appendEntriesRequest) (hterm : m.term = (σ.s i).currentTerm)
    (hfol : (σ.s i).state = follower) (hidx : index = m.prevLogIndex + 1)
    (hstep : σ.appendEntriesAlreadyDone i j index m = some σ') : SpecInv σ' := by
  subst hsrc hidx
  have hmm : m ∈ msgs σ := List.mem_append_left _ hm
  -- the request's commit index, within the durable log of its term's leader
  have hrc : ∀ l ∈ σ.server, (σ.s l).state = leader → (σ.s l).currentTerm = (σ.s i).currentTerm →
      m.commitIndex ≤ (σ.s l).durable.log.length :=
    fun l hl hll ht => h.reqCommit l hl hll m hmm hty (hterm.trans ht.symm)
  -- the response, fine to send in `σ` for an acknowledged index within the leader's durable log
  have hok : ∀ mi : Int, (∀ l ∈ σ.server, (σ.s l).state = leader → m.source = l →
      (σ.s l).currentTerm = (σ.s i).currentTerm → mi ≤ (σ.s l).durable.log.length) →
      MsgOk σ { type := .appendEntriesResponse, subtype := m.subtype, term := (σ.s i).currentTerm, success := true, matchIndex := mi, source := i, dest := m.source } := by
    intro mi hmi
    refine ⟨?_, ?_, ⟨Int.le_refl _, fun _ => ?_⟩, ?_, ?_, fun e he => by simp at he,
      fun hty' => absurd hty' (by simp)⟩
    · intro l _ _ k e hk; simp at hk
    · intro l hl hll
      refine ⟨fun _ hty' => absurd hty' (by simp), fun hd _ ht _ => ?_, fun hty' => absurd hty' (by simp)⟩
      change m.source = l at hd
      change (σ.s i).currentTerm = (σ.s l).currentTerm at ht
      have := hmi l hl hll hd ht.symm
      exact ⟨Int.le_trans this (h.2.1 l hl hll).1, fun _ => this⟩
    · show (σ.s i).currentTerm ≤ (σ.s m.source).currentTerm
      rw [← hterm]; exact (h.2.2.1 m hmm).1
    · intro l hl hc
      refine ⟨fun _ hty' => absurd hty' (by simp), fun hd _ _ => ?_, fun _ _ hty' => absurd hty' (by simp)⟩
      change m.source = l at hd
      show (σ.s i).currentTerm < (σ.s l).currentTerm
      rw [← hterm]; exact (h.2.2.2.1 l hl hc).1 m hmm hd hty
    · intro hne; exact absurd rfl hne
  -- an acknowledgement of the request's last index is within the leader's durable log
  have hlast : ∀ l ∈ σ.server, (σ.s l).state = leader → m.source = l →
      (σ.s l).currentTerm = (σ.s i).currentTerm → m.prevLogIndex + m.entries.length ≤ (σ.s l).durable.log.length :=
    fun l hl hll hd ht => (h.2.1 l hl hll).2.2.2.1 m hm hd hty (hterm.trans ht.symm)
  unfold State.appendEntriesAlreadyDone at hstep; dsimp only at hstep
  split at hstep
  · cases hstep
  · cases hstep
    have hfields : ∀ st : State, (∀ k, (st.s k).currentTerm = (σ.s k).currentTerm ∧ (st.s k).state = (σ.s k).state ∧
        (st.s k).log = (σ.s k).log ∧ (st.s k).durable = (σ.s k).durable ∧
        (σ.s k).commitIndex ≤ (st.s k).commitIndex) → st.server = σ.server →
        ∀ mi, MsgOk σ { type := .appendEntriesResponse, subtype := m.subtype, term := (σ.s i).currentTerm, success := true, matchIndex := mi, source := i, dest := m.source } →
        MsgOk (st.discard m) { type := .appendEntriesResponse, subtype := m.subtype, term := (σ.s i).currentTerm, success := true, matchIndex := mi, source := i, dest := m.source } :=
      fun st hst hsv mi hmo => msgOk_congr hmo hsv (fun k => (hst k).1) (fun k => (hst k).2.1)
        (fun k => (hst k).2.2.1) (fun k => (hst k).2.2.2.1) (fun k => (hst k).2.2.2.2)
    -- the acknowledged index, `i`'s commit index: within the leader's durable log (`CommitInDurable`)
    have hmi2 : ∀ l ∈ σ.server, (σ.s l).state = leader → m.source = l → (σ.s l).currentTerm = (σ.s i).currentTerm →
        m.subtype ≠ "heartbeat" → m.prevLogIndex + 1 ≤ (σ.s i).commitIndex →
        (σ.s i).commitIndex ≤ (σ.s l).durable.log.length :=
      fun l hl hll _ ht _ _ => h.commitInDurable i hi l hl hll ht.symm
    split
    · split
      · apply specInv_reply (specInv_commitTo_follower h hi hfol (fun l hl hll ht => Int.le_trans
          (Int.le_refl _) (hrc l hl hll ht)))
        exact hfields _ (fun k => commitTo_fields σ i _ k) rfl _ (hok _ (fun l hl hll hd ht => by
          split
          · exact hlast l hl hll hd ht
          · rename_i hc
            simp at hc
            exact hmi2 l hl hll hd ht hc.1 (by have := hc.2; omega)))
      · apply specInv_reply h
        exact hfields _ (fun k => ⟨rfl, rfl, rfl, rfl, Int.le_refl _⟩) rfl _ (hok _ (fun l hl hll hd ht => by
          split
          · exact hlast l hl hll hd ht
          · rename_i hc
            simp at hc
            exact hmi2 l hl hll hd ht hc.1 (by have := hc.2; omega)))
    · apply specInv_reply (specInv_commitTo_follower h hi hfol (fun l hl hll ht =>
        Int.le_trans (Int.min_le_left _ _) (hrc l hl hll ht)))
      exact hfields _ (fun k => commitTo_fields σ i _ k) rfl _ (hok _ (fun l hl hll hd ht => by
          split
          · exact hlast l hl hll hd ht
          · rename_i hc
            simp at hc
            exact hmi2 l hl hll hd ht hc.1 (by have := hc.2; omega)))

theorem mem_somes3 {a b c : Option State} {σ' : State} (h : σ' ∈ somes [a, b, c]) :
    a = some σ' ∨ b = some σ' ∨ c = some σ' := by
  unfold somes at h
  rw [List.mem_filterMap] at h
  obtain ⟨o, ho, he⟩ := h
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
  simp only [id] at he
  rcases ho with rfl | rfl | rfl
  · exact Or.inl he
  · exact Or.inr (Or.inl he)
  · exact Or.inr (Or.inr he)

/-- **`AcceptAppendEntriesRequest(i, j, logOk, m)`**, `m` an append request in `messages` from `j`,
not a snapshot. -/
theorem specInv_acceptAppendEntriesRequest {σ : State} {i j : ID} {logOk : Bool} {m : Etcdraft.Msg}
    {L : List State} (h : SpecInv σ) (hi : i ∈ σ.server) (hm : m ∈ σ.messages.domain)
    (hsrc : m.source = j) (hty : m.type = .appendEntriesRequest) (hsnap : m.subtype ≠ "snapshot")
    (hstep : σ.acceptAppendEntriesRequest i j logOk m = .ok L) : ∀ σ' ∈ L, SpecInv σ' := by
  unfold State.acceptAppendEntriesRequest at hstep; dsimp only at hstep
  split at hstep
  · simp only [pure, Except.pure, Except.ok.injEq] at hstep
    subst hstep; intro _ h; cases h
  · rename_i hg
    have hterm : m.term = (σ.s i).currentTerm := Classical.byContradiction fun hn => hg (by simp [hn])
    have hfol : (σ.s i).state = follower := Classical.byContradiction fun hn => hg (by simp [hn])
    split at hstep
    · rename_i hs; simp at hs; exact absurd hs hsnap
    · cases hc : σ.conflictAppendEntriesRequest i (m.prevLogIndex + 1) m with
      | error e => simp [hc, bind, Except.bind] at hstep
      | ok c =>
        cases hn : σ.noConflictAppendEntriesRequest i (m.prevLogIndex + 1) m with
        | error e => simp [hc, hn, bind, Except.bind] at hstep
        | ok n =>
          simp [hc, hn, bind, Except.bind, pure, Except.pure] at hstep
          subst hstep
          intro σ' hσ'
          have hmm : m ∈ msgs σ := List.mem_append_left _ hm
          rcases mem_somes3 hσ' with ha | ha | ha
          · exact specInv_appendEntriesAlreadyDone h hi hm hsrc hty hterm hfol rfl ha
          · subst ha; exact specInv_conflictAppendEntriesRequest h hi hfol hc
          · subst ha; exact specInv_noConflictAppendEntriesRequest h hi hfol hmm hterm rfl hn

theorem mem_somes2 {a b : Option State} {σ' : State} (h : σ' ∈ somes [a, b]) :
    a = some σ' ∨ b = some σ' := by
  unfold somes at h
  rw [List.mem_filterMap] at h
  obtain ⟨o, ho, he⟩ := h
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
  simp only [id] at he
  rcases ho with rfl | rfl
  · exact Or.inl he
  · exact Or.inr he

/-- **`HandleAppendEntriesRequest(i, j, m)`**, every successor: `m` an append request in `messages`
from `j` to `i`, not a snapshot; no `PreVote`, no `CheckQuorum`. -/
theorem specInv_handleAppendEntriesRequest {σ : State} {i j : ID} {m : Etcdraft.Msg} {L : List State}
    (h : SpecInv σ) (hi : i ∈ σ.server) (hm : m ∈ σ.messages.domain) (hsrc : m.source = j)
    (hty : m.type = .appendEntriesRequest) (hsnap : m.subtype ≠ "snapshot")
    (hpv : σ.preVote = false) (hcq : σ.checkQuorum = false)
    (hstep : σ.handleAppendEntriesRequest i j m = .ok L) : ∀ σ' ∈ L, SpecInv σ' := by
  unfold State.handleAppendEntriesRequest at hstep; dsimp only at hstep
  split at hstep
  · simp only [pure, Except.pure, Except.ok.injEq] at hstep
    subst hstep; intro _ h; cases h
  · simp only [bind, Except.bind] at hstep
    split at hstep
    · cases hstep
    · rename_i acc hacc
      simp only [pure, Except.pure, Except.ok.injEq] at hstep
      subst hstep
      have hout : ∀ lo : Bool, ∀ t ∈ somes [σ.rejectAppendEntriesRequest i j m lo, σ.returnToFollowerState i m] ++ acc,
          SpecInv t := by
        intro _ t ht
        rcases List.mem_append.mp ht with ht | ht
        · rcases mem_somes2 ht with ht | ht
          · exact specInv_rejectAppendEntriesRequest h hpv hcq ht
          · exact specInv_returnToFollowerState h hi ht
        · exact specInv_acceptAppendEntriesRequest h hi hm hsrc hty hsnap hacc t ht
      split
      · intro σ' hσ'
        obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hσ'
        exact specInv_upd_frame (hout _ t ht) rfl rfl rfl rfl rfl rfl rfl rfl
      · exact hout _

/-! ## `QuorumLogInv`'s fact at a follower's raised commit index (review round 3's B6(a)) -/

/-- **`QuorumLogInv`'s fact**: `TracedHooksDraft`'s `QuorumLogF`, restated here (which that file
imports; `QuorumLogF_eq` there says they are equal). -/
def QuorumLogS (σ : State) : Prop :=
  ∀ i ∈ σ.server, isQuorum ((σ.getConfig i).filter (fun j =>
    or (!σ.server.contains j) (!isPrefix (TraceSim.committedL σ i) (σ.s j).log))) (σ.getConfig i) = false

/-- **Two servers' committed prefixes are comparable**, `allFacts_logInv`'s statement for one pair. -/
def CommittedCmp (σ : State) (i k : ID) : Prop :=
  (or (isPrefix (TraceSim.committedL σ i) (TraceSim.committedL σ k))
    (isPrefix (TraceSim.committedL σ k) (TraceSim.committedL σ i))) = true

theorem isQuorum_filter_mono {c : SetIds} {p q : ID → Bool} (hpq : ∀ j ∈ c, p j = true → q j = true)
    (h : isQuorum (c.filter q) c = false) : isQuorum (c.filter p) c = false := by
  unfold isQuorum at h ⊢
  have hl : (c.filter p).length ≤ (c.filter q).length := by
    rw [← List.countP_eq_length_filter, ← List.countP_eq_length_filter]
    exact List.countP_mono_left hpq
  have hs : ∀ r : ID → Bool, SetIds.subset (c.filter r) c = true := by
    intro r; unfold SetIds.subset; rw [List.all_eq_true]
    intro x hx; simpa using (List.mem_filter.mp hx).1
  rw [hs] at h ⊢
  simp only [Bool.true_and, decide_eq_false_iff_not] at h ⊢
  omega

theorem prefix_of_isPrefix {s t : List Entry} (h : isPrefix s t = true) : s <+: t := by
  unfold isPrefix at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  rw [← h.2]; exact List.take_prefix _ _

/-- **`CommitTo(i, c)` keeps `QuorumLogInv`'s fact**, for `c` within the commit index of a server `src`
(`hc`, `hsl`: `src`'s committed prefix is `c` long at least) whose committed prefix is comparable with
`i`'s new one (`hcmp`): `i`'s new committed prefix is then a prefix of `src`'s, and every log
extending `src`'s extends it. `src`'s quorum condition is over `i`'s configuration: every server's is
the fixed one (`CfgFixed`). -/
theorem quorumLog_commitTo {σ : State} {i src : ID} {c : Int} (hq : QuorumLogS σ) (hsrc : src ∈ σ.server)
    (hc : c ≤ (σ.s src).commitIndex) (hsl : (σ.s src).commitIndex ≤ (σ.s src).log.length)
    (hcf : CfgFixed σ) (hcmp : CommittedCmp (σ.commitTo i c) i src) :
    QuorumLogS (σ.commitTo i c) := by
  have hs : ∀ k, (σ.commitTo i c).s k =
      if k = i then { σ.s i with commitIndex := max (σ.s i).commitIndex c } else σ.s k := fun _ => rfl
  have hlog : ∀ k, ((σ.commitTo i c).s k).log = (σ.s k).log := by
    intro k; rw [hs]; split <;> subst_vars <;> rfl
  have hcfg' : ∀ k, (σ.commitTo i c).getConfig k = σ.getConfig k := by
    intro k; unfold State.getConfig; rw [hs]; split <;> subst_vars <;> rfl
  have hsrv : (σ.commitTo i c).server = σ.server := rfl
  -- the committed prefixes: `k`'s kept unless `k` is `i` and its commit index rises
  have hcl : ∀ k, (k ≠ i ∨ c ≤ (σ.s i).commitIndex) →
      TraceSim.committedL (σ.commitTo i c) k = TraceSim.committedL σ k := by
    intro k hk
    unfold TraceSim.committedL; rw [hs]
    split
    · subst_vars
      rcases hk with hk | hk
      · exact absurd rfl hk
      · simp only; rw [Int.max_eq_left hk]
    · rfl
  intro k hk
  rw [hsrv] at hk
  simp only [hsrv, hcfg', hlog]
  by_cases hki : k ≠ i ∨ c ≤ (σ.s i).commitIndex
  · rw [hcl k hki]; exact hq k hk
  · simp only [not_or, Classical.not_not] at hki
    obtain ⟨rfl, hlt⟩ := hki
    have hsi : src ≠ k := by rintro rfl; omega
    have hB : TraceSim.committedL (σ.commitTo k c) src = TraceSim.committedL σ src := hcl src (Or.inl hsi)
    -- `k`'s new committed prefix is a prefix of `src`'s
    have hAB : TraceSim.committedL (σ.commitTo k c) k <+: TraceSim.committedL σ src := by
      have hlA : (TraceSim.committedL (σ.commitTo k c) k).length ≤ (TraceSim.committedL σ src).length := by
        unfold TraceSim.committedL; rw [hs]; simp only [↓reduceIte, List.length_take]; omega
      unfold CommittedCmp at hcmp; rw [hB] at hcmp
      rcases Bool.or_eq_true_iff.mp hcmp with hp | hp
      · exact prefix_of_isPrefix hp
      · have hp := prefix_of_isPrefix hp
        rw [hp.eq_of_length (Nat.le_antisymm hp.length_le hlA)]
        exact List.prefix_refl _
    have hcfg : σ.getConfig k = σ.getConfig src := by
      simp only [State.getConfig, hcf k hk, hcf src hsrc]
    rw [hcfg]
    refine isQuorum_filter_mono (fun j _ hp => ?_) (hq src hsrc)
    simp only [Bool.or_eq_true, Bool.not_eq_true'] at hp ⊢
    rcases hp with hp | hp
    · exact Or.inl hp
    · right
      cases hBj : isPrefix (TraceSim.committedL σ src) (σ.s j).log
      · rfl
      · rw [isPrefix_of_prefix _ _ (hAB.trans (prefix_of_isPrefix hBj))] at hp; cases hp

/-- A reply reads no server. -/
theorem quorumLog_reply (st : State) (r q : Etcdraft.Msg) : QuorumLogS (st.reply r q) = QuorumLogS st := rfl

theorem committedCmp_reply (st : State) (r q : Etcdraft.Msg) (a b : ID) :
    CommittedCmp (st.reply r q) a b = CommittedCmp st a b := rfl

/-- **`AppendEntriesAlreadyDone(i, j, index, m)` keeps `QuorumLogInv`'s fact** (with a heartbeat's
`CommitTo`, and an accepted or stale append's): `i`'s commit index rises to at most `m`'s, which is
within its sender's (`ReqCommitC`). What the simulation supplies: `hco`, `CommitOk` of the state
(`allFacts_commitOk`); `hcmp`, the committed prefixes of `i` and `m`'s sender in the new state
comparable (`allFacts_logInv` of the new state, from raft's ghost state after the step). -/
theorem quorumLog_appendEntriesAlreadyDone {σ σ' : State} {i j : ID} {index : Int} {m : Etcdraft.Msg}
    (h : SpecInv σ) (hq : QuorumLogS σ) (hm : m ∈ σ.messages.domain)
    (hty : m.type = .appendEntriesRequest) (hco : TraceSim.CommitOk σ)
    (hstep : σ.appendEntriesAlreadyDone i j index m = some σ') (hcmp : CommittedCmp σ' i m.source) :
    QuorumLogS σ' := by
  obtain ⟨hsrc, hcs⟩ := h.reqCommitC m (List.mem_append_left _ hm) hty
  have hsl := (hco m.source hsrc).2
  unfold State.appendEntriesAlreadyDone at hstep; dsimp only at hstep
  split at hstep
  · cases hstep
  · cases hstep
    rw [quorumLog_reply]; rw [committedCmp_reply] at hcmp
    split
    · rename_i h1; simp only [h1, ↓reduceIte] at hcmp
      split
      · rename_i h2; simp only [h2, ↓reduceIte] at hcmp
        exact quorumLog_commitTo hq hsrc hcs hsl h.cfgFixed hcmp
      · exact hq
    · rename_i h1; simp only [h1, ↓reduceIte] at hcmp
      exact quorumLog_commitTo hq hsrc (Int.le_trans (Int.min_le_left _ _) hcs) hsl h.cfgFixed hcmp

/-! ## `DurInv` itself is not preserved -/

/-- A single leader of term 1 with one entry it has not persisted yet (reachable: `ClientRequest`
after `BecomeLeader`, before `Ready`). -/
def cexConfig : Config := { incoming := [1], outgoing := [], learners := [] }

def cexDurable : Durable := { currentTerm := 1, votedFor := 1, log := [], commitIndex := 0, config := cexConfig }

def cexServer : Server :=
  { currentTerm := 1, state := leader, votedFor := 1, lead := 1, log := [{ term := 1, type := .value, value := .val 0 }], commitIndex := 0, votesResponded := [1], votesGranted := [1], matchIndex := fun _ => 0, pendingConfChangeIndex := 0, config := cexConfig, durable := cexDurable }

def cexState : State :=
  { server := [1], s := fun _ => cexServer, messages := [], pendingMessages := [], reconfigCount := 0 }

/-- **`DurInv` is not preserved by `AppendEntriesToSelf`**: its acknowledgement of the leader's whole
log goes to `pendingMessages`, beyond the durable log (only `Ready` hands it out, after persisting);
`DurInvFixed` leaves the pending self-acknowledgements out. -/
theorem durInv_not_preserved :
    DurInv cexState ∧ ∃ σ', cexState.appendEntriesToSelf 1 = some σ' ∧ ¬ DurInv σ' := by
  refine ⟨?_, _, rfl, ?_⟩
  · intro i _ _
    refine ⟨by simp [cexState, cexServer, cexDurable], fun j _ => by simp [cexState, cexServer, cexDurable], fun m hm => by simp [cexState, cexServer, cexDurable, Bag.domain] at hm,
      fun m hm => by simp [cexState, cexServer, cexDurable, Bag.domain] at hm⟩
  · intro hD
    have := (hD 1 (by simp [State.send, cexState]) rfl).2.2.2
      { type := .appendEntriesResponse, subtype := "app", term := 1, success := true, matchIndex := 1,
        source := 1, dest := 1 }
      (by simp [State.send, cexState, cexServer, cexDurable, Bag.with, Bag.add, Bag.domain]) rfl rfl
      (by simp [State.send, cexState, cexServer, cexDurable]) rfl
    simp [State.send, cexState, cexServer, cexDurable] at this

/-! ## The initial state -/

/-- **`Init`** satisfies the invariant when its initial configuration is the server set (as the
simulation's: `simInit`): no leader, no candidate, no message. -/
theorem specInv_init (server : SetIds) : SpecInv (init server server) := by
  have hl : ∀ i, ((init server server).s i).state ≠ leader := fun _ => follower_ne_leader
  have hc : ∀ i, ((init server server).s i).state ≠ candidate := fun _ => follower_ne_candidate
  refine ⟨fun i _ h => absurd h (hl i), fun i _ h => absurd h (hl i), fun m hm => ?_,
    fun i _ h => absurd h (hc i), fun m hm => ?_, fun _ _ l _ h => absurd h (hl l),
    fun l _ h => absurd h (hl l), fun m hm => ?_, fun l _ h => absurd h (hl l),
    ⟨fun k _ e he => ?_, fun m hm => ?_⟩, fun _ _ => rfl⟩ <;>
    first | simp [msgs, init, Bag.domain] at hm | simp [init] at he

end TraceSpecInv
end EtcdGrove
end Perennial
