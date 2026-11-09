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
        m.commitIndex ≤ (σ.s i).log.length)) ∧
  MsgTermOk σ m ∧
  (∀ i ∈ σ.server, (σ.s i).state = candidate →
      (m.source = i → m.type = .appendEntriesRequest → m.term < (σ.s i).currentTerm) ∧
      (m.dest = i → m.type = .appendEntriesResponse → m.success = true → m.term < (σ.s i).currentTerm) ∧
      (¬ persisted (σ.s i) → m.dest = i → m.type = .requestVoteResponse → m.voteGranted = true →
        m.term = (σ.s i).currentTerm → m.source = i)) ∧
  (m.entries ≠ [] → 0 ≤ m.prevLogIndex)

/-- A message with no entries that is neither an append request, a successful append response
nor a granted vote, of its source's term at most, is fine to send. -/
theorem msgOk_plain (σ : State) (m : Etcdraft.Msg) (he : m.entries = [])
    (hq : m.type ≠ .appendEntriesRequest) (hs : m.type = .appendEntriesResponse → m.success = false)
    (hv : m.type = .requestVoteResponse → m.voteGranted = false)
    (ht : m.term ≤ (σ.s m.source).currentTerm) : MsgOk σ m := by
  refine ⟨?_, ?_, ⟨ht, ?_⟩, ?_, ?_⟩
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
  obtain ⟨hLE, hD, hT, hC, hP, hCW, hRC⟩ := h
  obtain ⟨mLE, mD, mT, mC, mP⟩ := hm
  have hmem := mem_msgs_send σ m
  refine ⟨?_, ?_, ?_, ?_, ?_, hCW, ?_⟩
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

/-- **Fewer messages**: the same servers, and each bag's messages among the old ones. -/
theorem specInv_mono {σ σ' : State} (h : SpecInv σ) (hs : σ'.s = σ.s) (hsrv : σ'.server = σ.server)
    (hm : ∀ x ∈ σ'.messages.domain, x ∈ σ.messages.domain)
    (hp : ∀ x ∈ σ'.pendingMessages.domain, x ∈ σ.pendingMessages.domain) : SpecInv σ' := by
  have hmm : ∀ x ∈ msgs σ', x ∈ msgs σ := by
    intro x hx; unfold msgs at *
    rcases List.mem_append.mp hx with h | h
    · exact List.mem_append_left _ (hm x h)
    · exact List.mem_append_right _ (hp x h)
  obtain ⟨hLE, hD, hT, hC, hP, hCW, hRC⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi hl
    rw [hsrv] at hi; rw [hs] at hl ⊢
    obtain ⟨h1, h2⟩ := hLE i hi hl
    refine ⟨fun j hj => h1 j (hsrv ▸ hj), fun x hx => h2 x (hmm x hx)⟩
  · intro i hi hl
    rw [hsrv] at hi; rw [hs] at hl ⊢
    obtain ⟨a1, a2, a3, a4, a5, a6, a7⟩ := hD i hi hl
    exact ⟨a1, a2, a3, fun x hx => a4 x (hm x hx), fun x hx => a5 x (hp x hx),
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
    (hM : ∀ j, (σ'.s j).matchIndex = (σ.s j).matchIndex) : SpecInv σ' := by
  simp only [SpecInv, LeaderEntries, DurS, TermsLe, MsgTermOk, CandS, PrevOk, CommitWithinLeader,
    ReqCommit, msgs, persisted, hsrv, hm, hp, hT, hS, hL, hD, hV, hC, hM]
  exact h

/-- **A server's update that changes none of the fields the invariant reads** (its vote, its
known leader, the votes it has had answered). -/
theorem specInv_upd_frame {σ : State} {i : ID} {f : Server → Server} (h : SpecInv σ)
    (hT : (f (σ.s i)).currentTerm = (σ.s i).currentTerm) (hS : (f (σ.s i)).state = (σ.s i).state)
    (hL : (f (σ.s i)).log = (σ.s i).log) (hD : (f (σ.s i)).durable = (σ.s i).durable)
    (hV : (f (σ.s i)).votesGranted = (σ.s i).votesGranted)
    (hC : (f (σ.s i)).commitIndex = (σ.s i).commitIndex)
    (hM : (f (σ.s i)).matchIndex = (σ.s i).matchIndex) : SpecInv (σ.upd i f) := by
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
index kept; `hcw`: its commit index within the log of any leader of its new term (for its own
term, from `CommitWithinLeader`); `hcand`: a candidate, its messages as `CandS` says. -/
theorem specInv_upd_nonleader {σ : State} {i : ID} {f : Server → Server} (h : SpecInv σ)
    (hS : (f (σ.s i)).state ≠ leader) (hT : (σ.s i).currentTerm ≤ (f (σ.s i)).currentTerm)
    (hL : (f (σ.s i)).log = (σ.s i).log) (hC : (f (σ.s i)).commitIndex = (σ.s i).commitIndex)
    (hcw : ∀ l ∈ σ.server, l ≠ i → (σ.s l).state = leader →
      (σ.s l).currentTerm = (f (σ.s i)).currentTerm → (σ.s i).commitIndex ≤ (σ.s l).log.length)
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
  obtain ⟨hLE, hD, hTm, hCa, hP, hCW, hRC⟩ := h
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
  refine ⟨?_, ?_, ?_, ?_, hP, ?_, ?_⟩
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

/-- **A server becoming a follower.** -/
theorem specInv_upd_follower {σ : State} {i : ID} {f : Server → Server} (h : SpecInv σ)
    (hS : (f (σ.s i)).state = follower) (hT : (σ.s i).currentTerm ≤ (f (σ.s i)).currentTerm)
    (hL : (f (σ.s i)).log = (σ.s i).log) (hC : (f (σ.s i)).commitIndex = (σ.s i).commitIndex)
    (hcw : ∀ l ∈ σ.server, l ≠ i → (σ.s l).state = leader →
      (σ.s l).currentTerm = (f (σ.s i)).currentTerm → (σ.s i).commitIndex ≤ (σ.s l).log.length) :
    SpecInv (σ.upd i f) :=
  specInv_upd_nonleader h (by rw [hS]; exact follower_ne_leader) hT hL hC hcw
    (fun hc => absurd (hS.symm.trans hc) follower_ne_candidate)

/-- **`BecomeFollowerOfTerm(i, t)`** for a term `t` no lower than `i`'s; `hcw`: `i`'s commit index
within the log of any other leader of term `t` (raft: a leader's log holds the committed entries,
leader completeness; for `t` `i`'s own term it is `CommitWithinLeader`'s). -/
theorem specInv_becomeFollowerOfTerm {σ : State} {i : ID} {t : Int} (h : SpecInv σ)
    (ht : (σ.s i).currentTerm ≤ t)
    (hcw : ∀ l ∈ σ.server, l ≠ i → (σ.s l).state = leader → (σ.s l).currentTerm = t →
      (σ.s i).commitIndex ≤ (σ.s l).log.length) :
    SpecInv (σ.becomeFollowerOfTerm i t) :=
  specInv_upd_follower h rfl ht rfl rfl hcw

/-- **`StepDownToFollower(i)`.** -/
theorem specInv_stepDownToFollower {σ σ' : State} {i : ID} (h : SpecInv σ) (hi : i ∈ σ.server)
    (hstep : σ.stepDownToFollower i = some σ') : SpecInv σ' := by
  unfold State.stepDownToFollower at hstep; dsimp only at hstep
  split at hstep
  · cases hstep
    exact specInv_becomeFollowerOfTerm h (Int.le_refl _) (fun l hl _ hll ht => h.2.2.2.2.2.1 i hi l hl hll ht.symm)
  · cases hstep

/-- **`UpdateTerm(i, j, m)`**; `hcw`: `i`'s commit index within the log of any leader of `m`'s term
(raft: leader completeness, the committed entries are in every later leader's log). -/
theorem specInv_updateTerm {σ σ' : State} {i j : ID} {m : Etcdraft.Msg} (h : SpecInv σ)
    (hcw : ∀ l ∈ σ.server, (σ.s l).state = leader → (σ.s l).currentTerm = m.term →
      (σ.s i).commitIndex ≤ (σ.s l).log.length)
    (hstep : σ.updateTerm i j m = some σ') : SpecInv σ' := by
  unfold State.updateTerm at hstep
  split at hstep
  · cases hstep
  · cases hstep
    rename_i hc
    have : (σ.s i).currentTerm < m.term := by
      refine Classical.byContradiction (fun hlt => hc ?_)
      simp [hlt]
    exact specInv_becomeFollowerOfTerm h (Int.le_of_lt this) (fun l hl _ hll ht => hcw l hl hll ht)

/-- **`ReturnToFollowerState(i, m)`.** -/
theorem specInv_returnToFollowerState {σ σ' : State} {i : ID} {m : Etcdraft.Msg} (h : SpecInv σ)
    (hi : i ∈ σ.server) (hstep : σ.returnToFollowerState i m = some σ') : SpecInv σ' := by
  unfold State.returnToFollowerState at hstep; dsimp only at hstep
  split at hstep
  · cases hstep
  · cases hstep
    exact specInv_upd_follower h rfl (Int.le_refl _) rfl rfl
      (fun l hl _ hll ht => h.2.2.2.2.2.1 i hi l hl hll ht.symm)

/-- **States that agree** as in `specInv_congr`, but for the votes granted, which may differ except
at an unpersisted candidate with none. -/
theorem specInv_congr_v {σ σ' : State} (h : SpecInv σ) (hsrv : σ'.server = σ.server)
    (hm : σ'.messages.domain = σ.messages.domain) (hp : σ'.pendingMessages.domain = σ.pendingMessages.domain)
    (hT : ∀ j, (σ'.s j).currentTerm = (σ.s j).currentTerm) (hS : ∀ j, (σ'.s j).state = (σ.s j).state)
    (hL : ∀ j, (σ'.s j).log = (σ.s j).log) (hD : ∀ j, (σ'.s j).durable = (σ.s j).durable)
    (hC : ∀ j, (σ'.s j).commitIndex = (σ.s j).commitIndex)
    (hM : ∀ j, (σ'.s j).matchIndex = (σ.s j).matchIndex)
    (hV : ∀ j, (σ.s j).state = candidate → ¬ persisted (σ.s j) → (σ.s j).votesGranted = [] →
      (σ'.s j).votesGranted = []) : SpecInv σ' := by
  obtain ⟨hLE, hDu, hTm, hCa, hP, hCW, hRC⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
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
  · simp only [CommitWithinLeader, hsrv, hS, hT, hC, hL]; exact hCW
  · simp only [ReqCommit, msgs, hsrv, hm, hp, hS, hT, hL]; exact hRC

/-- `MsgOk` reads only the servers' terms, roles, logs and durable states. -/
theorem msgOk_congr {σ σ' : State} {m : Etcdraft.Msg} (h : MsgOk σ m) (hsrv : σ'.server = σ.server)
    (hT : ∀ j, (σ'.s j).currentTerm = (σ.s j).currentTerm) (hS : ∀ j, (σ'.s j).state = (σ.s j).state)
    (hL : ∀ j, (σ'.s j).log = (σ.s j).log) (hD : ∀ j, (σ'.s j).durable = (σ.s j).durable) :
    MsgOk σ' m := by
  simp only [MsgOk, MsgTermOk, persisted, hsrv, hT, hS, hL, hD]
  exact h

/-- A vote response is fine to send when it is of its source's term, a granted one also of its
destination's, and a granted one of an unpersisted candidate's term is the candidate's own. -/
theorem msgOk_vote (σ : State) (r : Etcdraft.Msg) (he : r.entries = [])
    (hty : r.type = .requestVoteResponse) (ht : r.term ≤ (σ.s r.source).currentTerm)
    (hg : r.voteGranted = true → r.term ≤ (σ.s r.dest).currentTerm)
    (hc : ∀ l ∈ σ.server, (σ.s l).state = candidate → ¬ persisted (σ.s l) → r.dest = l →
      r.voteGranted = true → r.term = (σ.s l).currentTerm → r.source = l) : MsgOk σ r := by
  refine ⟨?_, ?_, ⟨ht, ?_⟩, ?_, ?_⟩
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
    refine ⟨?_, ?_, ⟨Int.le_refl _, fun _ => Int.le_refl _⟩, ?_, ?_⟩
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
      · exact specInv_upd_frame h rfl rfl rfl rfl rfl rfl rfl
      · exact msgOk_congr (hok _ (fun _ => hgt)) rfl
          (fun k => by by_cases hk : k = i <;> simp [State.discard, upd_s, hk])
          (fun k => by by_cases hk : k = i <;> simp [State.discard, upd_s, hk])
          (fun k => by by_cases hk : k = i <;> simp [State.discard, upd_s, hk])
          (fun k => by by_cases hk : k = i <;> simp [State.discard, upd_s, hk])
    · rename_i hg
      apply specInv_reply h
      exact msgOk_congr (hok _ (fun h' => absurd h' hg)) rfl (fun _ => rfl) (fun _ => rfl)
        (fun _ => rfl) (fun _ => rfl)

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
    · refine specInv_congr_v (σ' := σ.upd i _) h rfl rfl rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_
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
    (hM : ∀ j ∈ σ.server, (σ.s j).state = leader → ∀ k,
      (σ'.s j).matchIndex k ≤ (σ.s j).durable.log.length) : SpecInv σ' := by
  obtain ⟨hLE, hDu, hTm, hCa, hP, hCW, hRC⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [LeaderEntries, hsrv, hm, hp, hT, hS, hL]; exact hLE
  · intro l hl hll
    rw [hsrv] at hl; rw [hS] at hll
    obtain ⟨a1, a2, -, a4, a5, a6, a7⟩ := hDu l hl hll
    simp only [hm, hp, hT, hL, hD, hC]
    exact ⟨a1, a2, hM l hl hll, a4, a5, a6, a7⟩
  · simp only [TermsLe, MsgTermOk, msgs, hm, hp, hT]; exact hTm
  · simp only [CandS, msgs, persisted, hsrv, hm, hp, hT, hS, hL, hD, hV]; exact hCa
  · simp only [PrevOk, msgs, hm, hp]; exact hP
  · simp only [CommitWithinLeader, hsrv, hS, hT, hC, hL]; exact hCW
  · simp only [ReqCommit, msgs, hsrv, hm, hp, hS, hT, hL]; exact hRC

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
      refine specInv_congr_m (σ' := σ.upd i _) h rfl rfl rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_
      all_goals try (intro k; by_cases hk : k = i <;> simp [upd_s, hk]; done)
      intro l hl hll k
      by_cases hli : l = i
      · subst hli
        obtain ⟨-, -, a3, -, -, a6, -⟩ := h.2.1 l hl hll
        rw [upd_s_self]
        dsimp only
        split
        · exact Int.max_le.mpr ⟨a3 _, a6 m hm hdst hty hterm hs⟩
        · exact a3 k
      · rw [upd_s_ne _ _ _ _ hli]; exact (h.2.1 l hl hll).2.2.1 k
    · exact h

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

/-- **`Timeout(i)`**; `hcw`: `i`'s commit index within the log of any leader of its new term (raft:
leader completeness). -/
theorem specInv_timeout {σ σ' : State} {i : ID} (h : SpecInv σ)
    (hcw : ∀ l ∈ σ.server, (σ.s l).state = leader → (σ.s l).currentTerm = (σ.s i).currentTerm + 1 →
      (σ.s i).commitIndex ≤ (σ.s l).log.length)
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
    apply specInv_upd_nonleader h (by simp only; exact candidate_ne_leader) (by simp only; omega) rfl rfl
      (fun l hl _ hll ht => hcw l hl hll ht)
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
  obtain ⟨hLE, hD, hTm, hCa, hP, hCW, hRC⟩ := h
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
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
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
      refine ⟨Int.le_refl _, Int.le_trans a2 a1, fun k => Int.le_trans (a3 k) a1, ?_, ?_, ?_, ?_⟩
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
    rw [hS] at hll; rw [hT, hT] at ht; rw [hC, hL]; exact hCW k hk l hl hll ht
  · intro l hl hll x hx hty ht
    rw [hS] at hll; rw [hT] at ht; rw [hL]; exact hRC l hl hll x (hA x hx) hty ht

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
    obtain ⟨hLE, hD, hTm, hCa, hP, hCW, hRC⟩ := h
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
    refine ⟨?_, ?_, ?_, ?_, hP, ?_, ?_⟩
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
      rw [hS] at hll; rw [hT, hT] at ht; rw [hC]
      exact Int.le_trans (hCW k hk l hl hll ht) (hlen l)
    · intro l hl hll x hx hty ht
      rw [hS] at hll; rw [hT] at ht
      exact Int.le_trans (hRC l hl hll x hx hty ht) (hlen l)

/-- **A server's new commit index**, every other field kept: within its durable log if a leader, and
within the log of every leader of its term. -/
theorem specInv_upd_commit {σ : State} {i : ID} {f : Server → Server} (h : SpecInv σ)
    (hT : (f (σ.s i)).currentTerm = (σ.s i).currentTerm) (hS : (f (σ.s i)).state = (σ.s i).state)
    (hL : (f (σ.s i)).log = (σ.s i).log) (hD : (f (σ.s i)).durable = (σ.s i).durable)
    (hV : (f (σ.s i)).votesGranted = (σ.s i).votesGranted)
    (hM : (f (σ.s i)).matchIndex = (σ.s i).matchIndex)
    (hcd : (σ.s i).state = leader → (f (σ.s i)).commitIndex ≤ (σ.s i).durable.log.length)
    (hcl : ∀ l ∈ σ.server, (σ.s l).state = leader → (σ.s l).currentTerm = (σ.s i).currentTerm →
      (f (σ.s i)).commitIndex ≤ (σ.s l).log.length) : SpecInv (σ.upd i f) := by
  obtain ⟨hLE, hDu, hTm, hCa, hP, hCW, hRC⟩ := h
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
  refine ⟨?_, ?_, ?_, ?_, hP, ?_, ?_⟩
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
    rw [hS'] at hll; rw [hT', hT'] at ht; rw [hL']
    by_cases hki : k = i
    · subst hki; rw [upd_s_self]; exact hcl l hl hll ht.symm
    · rw [upd_s_ne _ _ _ _ hki]; exact hCW k hk l hl hll ht
  · simp only [ReqCommit, hS', hT', hL']; exact hRC

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
    (hone : σ.moreThanOneLeaderInv = true) (hstep : σ.advanceCommitIndex i = some σ') : SpecInv σ' := by
  unfold State.advanceCommitIndex at hstep; dsimp only at hstep
  split at hstep
  · cases hstep
  · cases hstep
    rename_i hl
    have hl : (σ.s i).state = leader := by simpa using hl
    obtain ⟨-, a2, a3, -⟩ := h.2.1 i hi hl
    have hcw := h.2.2.2.2.2.1 i hi i hi hl rfl
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
            obtain ⟨k, hk⟩ := isQuorum_nonempty h3
            have hk := (List.mem_filter.mp hk).2
            simp only [decide_eq_true_eq] at hk
            have := a3 k
            constructor <;> omega
        · exact ⟨a2, hcw⟩)
    apply specInv_upd_commit h rfl rfl rfl rfl rfl rfl
    · intro _; exact hb.1
    · intro l hl' hll ht
      have := oneLeader hone hl' hi hll hl ht
      subst this
      exact hb.2
