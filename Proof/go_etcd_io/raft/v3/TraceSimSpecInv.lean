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
    (∀ j, (σ.s i).matchIndex j ≤ (σ.s i).durable.log.length) ∧
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

/-- **The append requests' commit indices**: an append request of a leader's term carries a commit
index within that leader's log (only the term's leader sends them, with its commit index). -/
def ReqCommit (σ : State) : Prop :=
  ∀ l ∈ σ.server, (σ.s l).state = leader → ∀ m ∈ msgs σ, m.type = .appendEntriesRequest →
    m.term = (σ.s l).currentTerm → m.commitIndex ≤ (σ.s l).log.length

/-- **The strengthened invariant.** -/
def SpecInv (σ : State) : Prop :=
  LeaderEntries σ ∧ DurS σ ∧ TermsLe σ ∧ CandS σ ∧ PrevOk σ ∧ CommitWithinLeader σ ∧ ReqCommit σ

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

theorem SpecInv.commitWithinLeader {σ : State} (h : SpecInv σ) : CommitWithinLeader σ := h.2.2.2.2.2.1

theorem SpecInv.durInvFixed {σ : State} (h : SpecInv σ) : DurInvFixed σ := by
  intro i hi hl
  obtain ⟨-, hc, hmi, hrq, -, hrm, hrp⟩ := h.2.1 i hi hl
  refine ⟨hc, fun j _ => hmi j, hrq, ?_⟩
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

end TraceSpecInv
end EtcdGrove
end Perennial
