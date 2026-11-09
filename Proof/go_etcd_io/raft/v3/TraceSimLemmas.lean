/-
Lean-first (no Rocq counterpart). Trace-check's layer B (2026-11-09): the pure facts the
simulation's per-rule lemmas rest on (`notes/trace-validation-sim.md`, revision 13): raft's log and
the specification's agree on their last term and length, and so on the up-to-date check of a vote.
-/
module

public import Proof.go_etcd_io.raft.v3.TraceSim

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open go_etcd_io.raft.v3

namespace TraceSim

variable [GooseExts]

/-! ## Sets of servers are canonical -/

theorem insertSorted_mem_iff (id x : Etcdraft.ID) :
    ∀ s : Etcdraft.SetIds, x ∈ Etcdraft.insertSorted id s ↔ x = id ∨ x ∈ s
  | [] => by simp [Etcdraft.insertSorted]
  | y :: ys => by
    unfold Etcdraft.insertSorted
    split
    · simp
    · split
      · rename_i h; subst h
        simp only [List.mem_cons]
        constructor
        · intro hx; exact Or.inr hx
        · rintro (hx | hx)
          · exact Or.inl hx
          · exact hx
      · rw [List.mem_cons, insertSorted_mem_iff id x ys, List.mem_cons]
        constructor
        · rintro (hx | hx | hx)
          · exact Or.inr (Or.inl hx)
          · exact Or.inl hx
          · exact Or.inr (Or.inr hx)
        · rintro (hx | hx | hx)
          · exact Or.inr (Or.inl hx)
          · exact Or.inl hx
          · exact Or.inr (Or.inr hx)

theorem setIds_mk_mem (l : List Etcdraft.ID) (x : Etcdraft.ID) : x ∈ Etcdraft.SetIds.mk l ↔ x ∈ l := by
  unfold Etcdraft.SetIds.mk
  suffices ∀ (l : List Etcdraft.ID) (s : Etcdraft.SetIds),
      x ∈ l.foldl (fun s id => Etcdraft.insertSorted id s) s ↔ x ∈ l ∨ x ∈ s by
    simpa using this l []
  intro l
  induction l with
  | nil => intro s; simp
  | cons y ys ih =>
    intro s
    rw [List.foldl_cons, ih, insertSorted_mem_iff, List.mem_cons]
    constructor
    · rintro (hx | hx | hx)
      · exact Or.inl (Or.inr hx)
      · exact Or.inl (Or.inl hx)
      · exact Or.inr hx
    · rintro ((hx | hx) | hx)
      · exact Or.inr (Or.inl hx)
      · exact Or.inl hx
      · exact Or.inr (Or.inr hx)

theorem insertSorted_sorted' (id : Etcdraft.ID) : ∀ s : Etcdraft.SetIds, s.Pairwise (· < ·) →
    (Etcdraft.insertSorted id s).Pairwise (· < ·)
  | [], _ => by simp [Etcdraft.insertSorted]
  | y :: ys, h => by
    unfold Etcdraft.insertSorted
    rw [List.pairwise_cons] at h
    split
    · rename_i hlt
      exact List.pairwise_cons.2 ⟨fun z hz => by
        rcases List.mem_cons.1 hz with rfl | hz
        · exact hlt
        · exact Nat.lt_trans hlt (h.1 z hz), List.pairwise_cons.2 h⟩
    · split
      · exact List.pairwise_cons.2 h
      · rename_i hge hne
        refine List.pairwise_cons.2 ⟨fun z hz => ?_, insertSorted_sorted' id ys h.2⟩
        rcases (insertSorted_mem_iff id z ys).1 hz with rfl | hz
        · exact Nat.lt_of_le_of_ne (Nat.le_of_not_lt hge) (fun e => hne e.symm)
        · exact h.1 z hz

theorem setIds_mk_sorted (l : List Etcdraft.ID) : (Etcdraft.SetIds.mk l).Pairwise (· < ·) := by
  unfold Etcdraft.SetIds.mk
  suffices ∀ (l : List Etcdraft.ID) (s : Etcdraft.SetIds), s.Pairwise (· < ·) →
      (l.foldl (fun s id => Etcdraft.insertSorted id s) s).Pairwise (· < ·) from this l [] List.Pairwise.nil
  intro l
  induction l with
  | nil => intro s h; exact h
  | cons y ys ih => intro s h; exact ih _ (insertSorted_sorted' y s h)

/-- Two lists with the same members make the same set. -/
theorem setIds_mk_eq (l1 l2 : List Etcdraft.ID) (h : ∀ x, x ∈ l1 ↔ x ∈ l2) :
    Etcdraft.SetIds.mk l1 = Etcdraft.SetIds.mk l2 := by
  have hs1 := setIds_mk_sorted l1
  have hs2 := setIds_mk_sorted l2
  have hp : (Etcdraft.SetIds.mk l1).Perm (Etcdraft.SetIds.mk l2) :=
    (List.perm_ext_iff_of_nodup (hs1.imp Nat.ne_of_lt) (hs2.imp Nat.ne_of_lt)).2 (fun x => by
      rw [setIds_mk_mem, setIds_mk_mem]; exact h x)
  exact List.Perm.eq_of_pairwise (fun a b _ _ hab hba => absurd (Nat.lt_trans hab hba) (Nat.lt_irrefl a)) hs1 hs2 hp

/-- A node's log in the shape the simulation needs: uncompacted (base `⟨0, 0⟩`), its indices
contiguous from 1, its bootstrap entries (the first `bl`) of term 1. -/
def LogShapeOk (bl : Nat) (s : PState) : Prop :=
  s.base = entryID.mk (W64 0) (W64 0) ∧ PlogWf s.base s.log ∧
  ∀ k e, k < bl → s.log[k]? = some e → e.Term' = W64 1

theorem logAbs_length (C : List w64) (bl first : Nat) (l : List EntryM) :
    (logAbs C bl first l).length = l.length := by
  unfold logAbs
  simp

/-- The specification's last term of the abstract log is raft's last term. -/
theorem lastTerm_logAbs (C : List w64) (bl : Nat) (s : PState) (h : LogShapeOk bl s) :
    Etcdraft.lastTerm (logAbs C bl 1 s.log) = uint.Z (plogLast s.base s.log).term' := by
  obtain ⟨hb, -, hboot⟩ := h
  unfold plogLast Etcdraft.lastTerm
  cases hl : s.log.getLast? with
  | none =>
    have : s.log = [] := List.getLast?_eq_none_iff.1 hl
    rw [hb]
    simp [this, logAbs]
    rfl
  | some e =>
    obtain ⟨l', hl'⟩ : ∃ l', s.log = l' ++ [e] := List.getLast?_eq_some_iff.1 hl
    have hlast : (logAbs C bl 1 s.log).getLast? = some (entAbs C bl (1 + l'.length) e) := by
      rw [hl']; unfold logAbs; simp [List.mapIdx_append]
    rw [hlast]
    simp only [entAbs]
    split
    · rename_i hk
      have h1 : e.Term' = W64 1 := hboot l'.length e (by omega) (by rw [hl']; simp)
      show (1 : Int) = uint.Z e.Term'
      rw [h1]; rfl
    · rfl

/-- Raft's last index is the abstract log's length. -/
theorem lastIndex_plogLast (bl : Nat) (s : PState) (h : LogShapeOk bl s) :
    uint.Z (plogLast s.base s.log).index' = s.log.length := by
  obtain ⟨hb, hwf, -⟩ := h
  unfold plogLast
  cases hl : s.log.getLast? with
  | none =>
    have : s.log = [] := List.getLast?_eq_none_iff.1 hl
    rw [hb, this]; rfl
  | some e =>
    obtain ⟨l', hl'⟩ : ∃ l', s.log = l' ++ [e] := List.getLast?_eq_some_iff.1 hl
    have he := hwf l'.length e (by rw [hl']; simp)
    rw [hb] at he
    simp only [entId]
    rw [he, hl']
    simp only [List.length_append, List.length_singleton]
    word

/-- The specification's `logOk` of a vote request is raft's `isUpToDate` of its last entry. -/
theorem logOk_iff_upToDate (C : List w64) (bl : Nat) (s : PState) (h : LogShapeOk bl s) (lt li : w64) :
    (uint.Z lt > Etcdraft.lastTerm (logAbs C bl 1 s.log) ∨
      (uint.Z lt = Etcdraft.lastTerm (logAbs C bl 1 s.log) ∧ uint.Z li ≥ (logAbs C bl 1 s.log).length)) ↔
    plogUpToDate s.base s.log (entryID.mk lt li) = true := by
  rw [lastTerm_logAbs C bl s h, logAbs_length]
  have hi := lastIndex_plogLast bl s h
  unfold plogUpToDate
  simp only [decide_eq_true_eq]
  constructor
  · rintro (h1 | ⟨h1, h2⟩)
    · left; exact h1
    · right; exact ⟨word.unsigned_inj h1, by rw [hi]; exact h2⟩
  · rintro (h1 | ⟨h1, h2⟩)
    · left; exact h1
    · right; exact ⟨by rw [h1], by rw [hi] at h2; exact h2⟩

theorem idAbs_inj {a b : w64} : idAbs a = idAbs b ↔ a = b := by
  unfold idAbs
  constructor
  · intro h; exact word.unsigned_inj (by have := congrArg (fun n : Nat => (n : Int)) h; simpa using this)
  · intro h; rw [h]

theorem idAbs_zero {a : w64} : idAbs a = Etcdraft.nil ↔ a = W64 0 := by
  have : Etcdraft.nil = idAbs (W64 0) := rfl
  rw [this, idAbs_inj]

/-- **A vote request of the node's term** (the rules `grantVote`/`rejectVote`, made exact): the
specification grants it exactly when raft does (`PCanVote` and up to date), and the node's server
after the specification's handling is related to raft's state after its vote. -/
theorem sim_vote_grant (C : List w64) (bl : Nat) (s : PState) (a : Etcdraft.Server) (src lt li : w64)
    (hR : SimServerR C bl s a) (hL : LogShapeOk bl s) :
    let logOk := or (decide (uint.Z lt > Etcdraft.lastTerm a.log))
      (and (decide (uint.Z lt = Etcdraft.lastTerm a.log)) (decide (uint.Z li ≥ a.log.length)))
    let grantSpec := and logOk (or (a.votedFor == idAbs src) (and (a.votedFor == Etcdraft.nil) (a.lead == Etcdraft.nil)))
    (grantSpec = true ↔ (PCanVote s src ∧ plogUpToDate s.base s.log (entryID.mk lt li) = true)) ∧
    (grantSpec = true → SimServerR C bl { s with vote := src } { a with votedFor := idAbs src }) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := hR
  have hok := logOk_iff_upToDate C bl s hL lt li
  rw [← h6] at hok
  refine ⟨?_, ?_⟩
  · simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq, PCanVote]
    rw [h3, h4, idAbs_inj, idAbs_zero, idAbs_zero]
    constructor
    · rintro ⟨hl, hv⟩
      refine ⟨hv, hok.1 ?_⟩
      rcases hl with hl | ⟨hl1, hl2⟩
      · exact Or.inl hl
      · exact Or.inr ⟨hl1, hl2⟩
    · rintro ⟨hv, hu⟩
      refine ⟨?_, hv⟩
      rcases hok.2 hu with hl | ⟨hl1, hl2⟩
      · exact Or.inl hl
      · exact Or.inr ⟨hl1, hl2⟩
  · intro _
    exact ⟨h1, h2, rfl, h4, h5, h6, h7, h8, h9, h10, h11⟩

/-- **A message of a later term** (the rule `higherTerm`, before the handling): the specification's
`UpdateTerm` (`BecomeFollowerOfTerm`) and raft's `becomeFollower` without a leader agree; a message
from a leader then sets `lead` in both, at the handling (`padoptLeader`, the handler's `lead' = j`). -/
theorem sim_higherTerm (C : List w64) (bl : Nat) (s : PState) (a : Etcdraft.Server) (t : w64)
    (hR : SimServerR C bl s a) (ht : uint.Z s.term < uint.Z t) :
    SimServerR C bl (pbecomeFollower s t (W64 0))
      { a with currentTerm := uint.Z t, state := Etcdraft.follower, lead := Etcdraft.nil,
               votedFor := if a.currentTerm != uint.Z t then Etcdraft.nil else a.votedFor } := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := hR
  have hne : t ≠ s.term := fun h => by rw [h] at ht; exact Int.lt_irrefl _ ht
  have hne' : a.currentTerm != uint.Z t := by
    rw [h1]; simp only [bne_iff_ne, ne_eq]; intro h; exact hne (word.unsigned_inj h).symm
  refine ⟨rfl, rfl, ?_, rfl, h5, h6, h7, h8, h9, ?_, ?_⟩
  · simp only [hne', ↓reduceIte, pbecomeFollower, hne]; rfl
  · intro h; cases h
  · intro h; cases h

/-- **A campaign** (the rule `campaign`, its `becomeCandidate`; PreVote off): the specification's
`Timeout(i)` and raft's `becomeCandidate` agree (the vote requests and the self vote that follow are
the trace's `SendRequestVote*` lines, `RequestVote(i, j)`). -/
theorem sim_campaign (C : List w64) (bl : Nat) (s : PState) (a : Etcdraft.Server) (id : w64)
    (hR : SimServerR C bl s a) (ht : uint.Z s.term + 1 < 2 ^ 64) :
    SimServerR C bl (pbecomeCandidate id s)
      { a with state := Etcdraft.candidate, currentTerm := a.currentTerm + 1, votedFor := idAbs id,
               lead := Etcdraft.nil, votesResponded := [], votesGranted := [] } := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := hR
  refine ⟨?_, rfl, rfl, rfl, h5, h6, h7, h8, h9, ?_, ?_⟩
  · simp only [pbecomeCandidate]; rw [h1]; word
  · intro _; simp [pbecomeCandidate, GMap.toList_empty]; rfl
  · intro h; cases h

/-- Membership of the abstract keys of a vote map. -/
theorem mem_keysAbs (m : GMap w64 Bool) (x : Etcdraft.ID) :
    x ∈ (GMap.toList m).map (fun p => idAbs p.1) ↔ ∃ k v, m !! k = some v ∧ idAbs k = x := by
  simp only [List.mem_map]
  constructor
  · rintro ⟨⟨k, v⟩, hm, hx⟩; exact ⟨k, v, (GMap.mem_toList m k v).1 hm, hx⟩
  · rintro ⟨k, v, hm, hx⟩; exact ⟨⟨k, v⟩, (GMap.mem_toList m k v).2 hm, hx⟩

/-- Membership of the abstract granted keys of a vote map. -/
theorem mem_grantedAbs (m : GMap w64 Bool) (x : Etcdraft.ID) :
    x ∈ ((GMap.toList m).filter (fun p => p.2)).map (fun p => idAbs p.1) ↔
      ∃ k, m !! k = some true ∧ idAbs k = x := by
  simp only [List.mem_map, List.mem_filter]
  constructor
  · rintro ⟨⟨k, v⟩, ⟨hm, hv⟩, hx⟩
    simp only at hv; subst hv
    exact ⟨k, (GMap.mem_toList m k _).1 hm, hx⟩
  · rintro ⟨k, hm, hx⟩; exact ⟨⟨k, true⟩, ⟨(GMap.mem_toList m k true).2 hm, rfl⟩, hx⟩

/-- **A vote response at a candidate** (the rule `recordVote`), its sender's first in the term (raft
records only a first response; the simulation's invariant: one `MsgVote` per campaign, no
duplication): the specification's `HandleRequestVoteResponse` and raft agree on the tally. -/
theorem sim_recordVote (C : List w64) (bl : Nat) (s : PState) (a : Etcdraft.Server) (src : w64) (v : Bool)
    (hR : SimServerR C bl s a) (hc : s.role = .candidate) (hnew : s.votes !! src = none) :
    SimServerR C bl { s with votes := recordVote s.votes src v }
      { a with votesResponded := a.votesResponded.add (idAbs src),
               votesGranted := if v then a.votesGranted.add (idAbs src) else a.votesGranted } := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := hR
  obtain ⟨hvr, hvg⟩ := h10 hc
  have hrv : recordVote s.votes src v = <[src := v]> s.votes := by
    unfold recordVote; rw [hnew]
  refine ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, ?_, ?_⟩
  · intro _
    simp only [hrv]
    constructor
    · rw [hvr]; unfold Etcdraft.SetIds.add Etcdraft.SetIds.union
      apply setIds_mk_eq; intro x
      rw [List.mem_append, setIds_mk_mem, mem_keysAbs, mem_keysAbs, List.mem_singleton]
      constructor
      · rintro (⟨k, w, hk, rfl⟩ | rfl)
        · by_cases hks : k = src
          · subst hks; exact ⟨k, v, GMap.lookup_insert _ _ _, rfl⟩
          · exact ⟨k, w, by rw [GMap.lookup_insert_ne _ _ (Ne.symm hks)]; exact hk, rfl⟩
        · exact ⟨src, v, GMap.lookup_insert _ _ _, rfl⟩
      · rintro ⟨k, w, hk, rfl⟩
        by_cases hks : k = src
        · subst hks; exact Or.inr rfl
        · rw [GMap.lookup_insert_ne _ _ (Ne.symm hks)] at hk; exact Or.inl ⟨k, w, hk, rfl⟩
    · cases v
      · simp only [Bool.false_eq_true, ↓reduceIte]
        rw [hvg]; apply setIds_mk_eq; intro x
        rw [mem_grantedAbs, mem_grantedAbs]
        constructor
        · rintro ⟨k, hk, rfl⟩
          by_cases hks : k = src
          · subst hks; rw [hnew] at hk; cases hk
          · exact ⟨k, by rw [GMap.lookup_insert_ne _ _ (Ne.symm hks)]; exact hk, rfl⟩
        · rintro ⟨k, hk, rfl⟩
          by_cases hks : k = src
          · subst hks; rw [GMap.lookup_insert] at hk; cases hk
          · exact ⟨k, by rw [GMap.lookup_insert_ne _ _ (Ne.symm hks)] at hk; exact hk, rfl⟩
      · simp only [↓reduceIte]
        rw [hvg]; unfold Etcdraft.SetIds.add Etcdraft.SetIds.union
        apply setIds_mk_eq; intro x
        rw [List.mem_append, setIds_mk_mem, mem_grantedAbs, mem_grantedAbs, List.mem_singleton]
        constructor
        · rintro (⟨k, hk, rfl⟩ | rfl)
          · by_cases hks : k = src
            · subst hks; rw [hnew] at hk; cases hk
            · exact ⟨k, by rw [GMap.lookup_insert_ne _ _ (Ne.symm hks)]; exact hk, rfl⟩
          · exact ⟨src, GMap.lookup_insert _ _ _, rfl⟩
        · rintro ⟨k, hk, rfl⟩
          by_cases hks : k = src
          · subst hks; exact Or.inr rfl
          · rw [GMap.lookup_insert_ne _ _ (Ne.symm hks)] at hk; exact Or.inl ⟨k, hk, rfl⟩
  · intro h; rw [hc] at h; cases h

/-- Raft's `lastIndex()` is the abstract log's length. -/
theorem plastIndex_length (bl : Nat) (s : PState) (h : LogShapeOk bl s) :
    uint.Z (plastIndex s) = s.log.length := by
  have hl := lastIndex_plogLast bl s h
  have hb : uint.Z (plogLast s.base s.log).index' < 2 ^ 64 := by word
  obtain ⟨hb0, -, -⟩ := h
  unfold plastIndex plogLastIndexZ
  rw [hb0]
  have : uint.Z (W64 0) = 0 := rfl
  rw [this]
  word

/-- **A candidate becomes leader** (`becomeLeader` up to `traceBecomeLeader`, after `reset`: the
won tally is the simulation's ghost, so the specification's guard is not this lemma's): the
specification's `BecomeLeader(i)` update. -/
theorem sim_becomeLeader (C : List w64) (bl : Nat) (s : PState) (a : Etcdraft.Server) (id : w64)
    (mt : GMap w64 w64) (hR : SimServerR C bl s a) (hs : LogShapeOk bl s) (hm : LeaderMatchOk id s mt) :
    SimServerR C bl (pbecomeLeader id s mt)
      { a with state := Etcdraft.leader, lead := idAbs id,
               matchIndex := fun j => if j = idAbs id then (a.log.length : Int) else 0 } := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := hR
  obtain ⟨hmi, hmo⟩ := hm
  refine ⟨h1, rfl, h3, rfl, h5, h6, h7, h8, h9, ?_, ?_⟩
  · intro h; cases h
  · intro _ j _
    simp only [pbecomeLeader]
    by_cases hj : j = id
    · subst hj
      simp only [↓reduceIte, hmi, Option.getD_some]
      rw [plastIndex_length bl s hs, h6, logAbs_length]
    · have hne : idAbs j ≠ idAbs id := fun e => hj (idAbs_inj.1 e)
      simp only [hne, ↓reduceIte]
      cases hx : mt !! j with
      | none => rfl
      | some x => rw [hmo j x hj hx]; rfl

/-- **An entry appended at a leader** (`appendEntry`: the new leader's empty entry, a proposal),
past the bootstrap entries and at the node's term: the specification's `ClientRequest(i, 0)`
(`Replicate`). -/
theorem sim_append (C : List w64) (bl : Nat) (s : PState) (a : Etcdraft.Server) (e : EntryM)
    (hR : SimServerR C bl s a) (hb : bl ≤ s.log.length) (he : e.Term' = s.term) :
    SimServerR C bl (pappend s [e])
      { a with log := a.log ++ [{ term := a.currentTerm, type := .value, value := .val 0 }] } := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := hR
  refine ⟨h1, h2, h3, h4, h5, ?_, h7, h8, h9, h10, h11⟩
  simp only [pappend, h6, logAbs, List.mapIdx_append, List.mapIdx_singleton]
  congr 2
  simp only [entAbs, he, h1]
  split
  · omega
  · rfl

/-! ### Append requests -/

/-- An abstract entry's term is raft's, where raft's bootstrap entries have term 1. -/
theorem entAbs_term (C : List w64) (bl k : Nat) (e : EntryM) (h : k ≤ bl → e.Term' = W64 1) :
    (entAbs C bl k e).term = uint.Z e.Term' := by
  unfold entAbs
  split
  · rename_i hk; rw [h hk]; rfl
  · rfl

theorem logAbs_getElem? (C : List w64) (bl first : Nat) (l : List EntryM) (k : Nat) :
    (logAbs C bl first l)[k]? = l[k]?.map (entAbs C bl (first + k)) := by
  unfold logAbs; rw [List.getElem?_mapIdx]

/-- The bootstrap entries of a list starting at index `first` have term 1. -/
def BootTerms (bl first : Nat) (l : List EntryM) : Prop :=
  ∀ k e, first + k ≤ bl → l[k]? = some e → e.Term' = W64 1

theorem BootTerms.take {bl first : Nat} {l : List EntryM} (h : BootTerms bl first l) (n : Nat) :
    BootTerms bl first (l.take n) := by
  intro k e hk he
  rw [List.getElem?_take] at he
  split at he
  · exact h k e hk he
  · cases he

/-- **`HasNoConflict` is raft's term match**: on the abstract log of the first `n` entries of a log
(from index 1), the abstract batch after index `p` has no conflict exactly when every entry of the
batch the log has carries the log's term. -/
theorem hasNoConflict_abs (st : Etcdraft.State) (i : Etcdraft.ID) (C : List w64) (bl p : Nat)
    (es ents : List EntryM) (hl : (st.s i).log = logAbs C bl 1 es) (hp : p ≤ es.length)
    (hbl : BootTerms bl 1 es) (hbe : BootTerms bl (p + 1) ents) :
    st.hasNoConflict i ((p : Int) + 1) (logAbs C bl (p + 1) ents) = true ↔
      ∀ k e, ents[k]? = some e → p + k < es.length → (es[p + k]?).map EntryM.Term' = some e.Term' := by
  unfold Etcdraft.State.hasNoConflict
  rw [hl]; simp only []
  rw [logAbs_length, logAbs_length]
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range,
    Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, beq_iff_eq]
  constructor
  · rintro ⟨-, h⟩ k e hk hpk
    have hkl : k < ents.length := (List.getElem?_eq_some_iff.1 hk).1
    rcases h k hkl with h | h
    · omega
    · have : ((p : Int) + 1 + k - 1).toNat = p + k := by omega
      rw [this, logAbs_getElem?, logAbs_getElem?, hk] at h
      obtain ⟨x, hx⟩ : ∃ x, es[p + k]? = some x := ⟨es[p + k], List.getElem?_eq_getElem hpk⟩
      rw [hx] at h ⊢
      simp only [Option.map_some, Option.some.injEq] at h ⊢
      rw [entAbs_term C bl _ x (fun hb => hbl (p + k) x (by omega) hx),
        entAbs_term C bl _ e (fun hb => hbe k e hb hk)] at h
      exact uint_Z_inj.mp h
  · intro h
    refine ⟨by omega, fun k hk => ?_⟩
    by_cases hpk : p + k < es.length
    · right
      have : ((p : Int) + 1 + k - 1).toNat = p + k := by omega
      rw [this, logAbs_getElem?, logAbs_getElem?]
      obtain ⟨e, he⟩ : ∃ e, ents[k]? = some e := ⟨ents[k], List.getElem?_eq_getElem hk⟩
      obtain ⟨x, hx⟩ : ∃ x, es[p + k]? = some x := ⟨es[p + k], List.getElem?_eq_getElem hpk⟩
      have := h k e he hpk
      rw [hx] at this ⊢; rw [he]
      simp only [Option.map_some, Option.some.injEq] at this ⊢
      rw [entAbs_term C bl _ x (fun hb => hbl (p + k) x (by omega) hx),
        entAbs_term C bl _ e (fun hb => hbe k e hb he), this]
    · left; omega

/-- An uncompacted log's term at a positive index. -/
theorem plogTermAt_base0 (es : List EntryM) (i : w64) (hi : 0 < uint.Z i) :
    plogTermAt (entryID.mk (W64 0) (W64 0)) es i = es[uint.nat i - 1]?.map EntryM.Term' := by
  unfold plogTermAt
  have h0 : uint.Z (entryID.mk (W64 0) (W64 0)).index' = 0 := rfl
  have h1 : ¬ uint.Z i < 0 := by omega
  have h2 : ¬ uint.Z i = 0 := by omega
  simp only [h0, h1, h2, ↓reduceIte]
  have : (uint.Z i - 0 - 1).toNat = uint.nat i - 1 := by word
  rw [this]; rfl

/-- Raft's `matchTerm` of a batch entry, on an uncompacted log: the log has an entry there, of the
same term. -/
theorem plogMatches_base0 (es : List EntryM) (e : EntryM) (q : Nat) (hq : uint.Z e.Index' = q + 1) :
    PlogMatches (entryID.mk (W64 0) (W64 0)) es (entId e) ↔ es[q]?.map EntryM.Term' = some e.Term' := by
  unfold PlogMatches entId
  simp only
  rw [plogTermAt_base0 es _ (by omega)]
  have : uint.nat e.Index' - 1 = q := by word
  rw [this]

theorem subSeqM_init (l : List Etcdraft.Entry) :
    Etcdraft.subSeqM l 1 ((l.length : Int) - 1) = .ok (l.take (l.length - 1)) := by
  unfold Etcdraft.subSeqM Etcdraft.subSeq
  by_cases h : (1 : Int) > (l.length : Int) - 1
  · have : l.length - 1 = 0 := by omega
    simp only [h, ↓reduceIte, this, List.take_zero]; rfl
  · have h2 : ¬ ((1 : Int) < 1 ∨ (l.length : Int) - 1 > l.length) := by omega
    simp only [h, h2, ↓reduceIte]
    have : ((l.length : Int) - 1).toNat - 1 + 1 = l.length - 1 := by omega
    simp only [Int.toNat_one, Nat.sub_self, List.drop_zero]
    rw [this]; rfl

theorem subSeqM_drop (l : List Etcdraft.Entry) (d : Nat) :
    Etcdraft.subSeqM l ((d : Int) + 1) l.length = .ok (l.drop d) := by
  unfold Etcdraft.subSeqM Etcdraft.subSeq
  by_cases h : (d : Int) + 1 > l.length
  · simp only [h, ↓reduceIte, List.drop_eq_nil_of_le (by omega : l.length ≤ d)]; rfl
  · have h2 : ¬ ((d : Int) + 1 < 1 ∨ (l.length : Int) > l.length) := by omega
    simp only [h, h2, ↓reduceIte]
    have : ((d : Int) + 1).toNat - 1 = d := by omega
    rw [this, List.take_of_length_le (by simp; omega)]; rfl

/-- The abstract log after a truncation to `q` and the batch from `d` on, `q = p + d`. -/
theorem logAbs_truncAppend (C : List w64) (bl p d : Nat) (es ents : List EntryM)
    (hq : p + d ≤ es.length) :
    logAbs C bl 1 (es.take (p + d)) ++ (logAbs C bl (p + 1) ents).drop d =
      logAbs C bl 1 (es.take (p + d) ++ ents.drop d) := by
  apply List.ext_getElem?
  intro k
  rw [logAbs_getElem?, List.getElem?_append, List.getElem?_append]
  simp only [logAbs_length, List.length_take, Nat.min_eq_left hq]
  split
  · rw [logAbs_getElem?]
  · rw [List.getElem?_drop, logAbs_getElem?, List.getElem?_drop]
    congr 1; funext e; congr 1; omega

/-- **`ConflictAppendEntriesRequest`** on raft's abstract log of `n` entries, while the batch
conflicts with it: the last entry is dropped. -/
theorem conflict_step (st : Etcdraft.State) (i : Etcdraft.ID) (m : Etcdraft.Msg) (C : List w64)
    (bl p n : Nat) (es ents : List EntryM) (hlog : (st.s i).log = logAbs C bl 1 (es.take n))
    (hents : m.entries = logAbs C bl (p + 1) ents) (hn : n ≤ es.length) (hpn : p ≤ n)
    (hc : (st.s i).commitIndex < (p : Int) + 1) (hne : ents ≠ [])
    (hbl : BootTerms bl 1 es) (hbe : BootTerms bl (p + 1) ents)
    (hconf : ¬ ∀ k e, ents[k]? = some e → p + k < n → ((es.take n)[p + k]?).map EntryM.Term' = some e.Term') :
    st.conflictAppendEntriesRequest i ((p : Int) + 1) m =
      .ok (some (st.upd i (fun v => { v with log := logAbs C bl 1 (es.take (n - 1)) }))) := by
  have hlen : (es.take n).length = n := by simp; omega
  have hnc : st.hasNoConflict i ((p : Int) + 1) m.entries = false := by
    rw [hents]
    cases h : st.hasNoConflict i ((p : Int) + 1) (logAbs C bl (p + 1) ents)
    · rfl
    · exfalso; apply hconf
      have := (hasNoConflict_abs st i C bl p (es.take n) ents hlog (by omega) (hbl.take n) hbe).1 h
      rw [hlen] at this; exact this
  unfold Etcdraft.State.conflictAppendEntriesRequest
  have hne' : m.entries.isEmpty = false := by
    rw [hents]; cases ents with
    | nil => exact absurd rfl hne
    | cons _ _ => simp [logAbs]
  simp only [hne', hnc, hc, decide_true, Bool.not_false, Bool.not_true, Bool.and_self,
    Bool.false_eq_true, ↓reduceIte]
  rw [hlog]
  have := subSeqM_init (logAbs C bl 1 (es.take n))
  rw [logAbs_length, hlen] at this
  rw [logAbs_length, hlen]
  simp only [bind, Except.bind, this, pure, Except.pure]
  have hl : (logAbs C bl 1 (List.take n es)).take (n - 1) = logAbs C bl 1 (List.take (n - 1) es) := by
    apply List.ext_getElem?; intro k
    rw [List.getElem?_take, logAbs_getElem?, logAbs_getElem?, List.getElem?_take, List.getElem?_take]
    split <;> (try split) <;> first | rfl | omega
  rw [hl]

/-- `upd` reads the function only at the updated server. -/
theorem upd_congr (st : Etcdraft.State) (i : Etcdraft.ID) (f g : Etcdraft.Server → Etcdraft.Server)
    (h : f (st.s i) = g (st.s i)) : st.upd i f = st.upd i g := by
  unfold Etcdraft.State.upd; rw [h]

/-- **`NoConflictAppendEntriesRequest`** on raft's abstract log `L` (`q` entries), the batch not
conflicting with it and reaching past it: the batch's entries past `q` are appended. -/
theorem noConflict_step (st : Etcdraft.State) (i : Etcdraft.ID) (m : Etcdraft.Msg) (C : List w64)
    (bl p : Nat) (L ents : List EntryM) (hlog : (st.s i).log = logAbs C bl 1 L)
    (hents : m.entries = logAbs C bl (p + 1) ents) (hprev : m.prevLogIndex = p) (hpq : p ≤ L.length)
    (hq : L.length < p + ents.length) (hc : (st.s i).commitIndex < (p : Int) + 1)
    (hbl : BootTerms bl 1 L) (hbe : BootTerms bl (p + 1) ents)
    (hnc : ∀ k e, ents[k]? = some e → p + k < L.length → (L[p + k]?).map EntryM.Term' = some e.Term') :
    st.noConflictAppendEntriesRequest i ((p : Int) + 1) m =
      .ok (some (st.upd i (fun v => { v with
        log := logAbs C bl 1 L ++ (logAbs C bl (p + 1) ents).drop (L.length - p) }))) := by
  have hnc' : st.hasNoConflict i ((p : Int) + 1) m.entries = true := by
    rw [hents]; exact (hasNoConflict_abs st i C bl p L ents hlog hpq hbl hbe).2 hnc
  have hne' : m.entries.isEmpty = false := by
    rw [hents]; cases ents with
    | nil => simp at hq; omega
    | cons _ _ => simp [logAbs]
  have hlt : (p : Int) + (m.entries.length : Int) > ((st.s i).log.length : Int) := by
    rw [hents, hlog, logAbs_length, logAbs_length]; omega
  unfold Etcdraft.State.noConflictAppendEntriesRequest
  simp only [hne', hnc', hc, hprev, hlt, decide_true, Bool.not_false, Bool.not_true, Bool.and_self,
    Bool.false_eq_true, ↓reduceIte]
  have hidx : ((st.s i).log.length : Int) - ((p : Int) + 1) + 2 = ((L.length - p : Nat) : Int) + 1 := by
    rw [hlog, logAbs_length]; omega
  rw [hidx, hents]
  have := subSeqM_drop (logAbs C bl (p + 1) ents) (L.length - p)
  simp only [bind, Except.bind, this, pure, Except.pure]
  congr 2; apply upd_congr; rw [hlog]

/-- **`AppendEntriesAlreadyDone`** of an append request past the commit index whose entries the
abstract log `L` all has: the commit index advanced to the request's (at most its last entry), the
success reply at its last entry. -/
theorem alreadyDone_accept (st : Etcdraft.State) (i j : Etcdraft.ID) (m : Etcdraft.Msg) (C : List w64)
    (bl p : Nat) (L ents : List EntryM) (hlog : (st.s i).log = logAbs C bl 1 L)
    (hents : m.entries = logAbs C bl (p + 1) ents) (hprev : m.prevLogIndex = p)
    (hq : p + ents.length ≤ L.length) (hc : (st.s i).commitIndex < (p : Int) + 1) (hne : ents ≠ [])
    (hsub : m.subtype ≠ "heartbeat") (hbl : BootTerms bl 1 L) (hbe : BootTerms bl (p + 1) ents)
    (hnc : ∀ k e, ents[k]? = some e → p + k < L.length → (L[p + k]?).map EntryM.Term' = some e.Term') :
    st.appendEntriesAlreadyDone i j ((p : Int) + 1) m =
      some ((st.commitTo i (min m.commitIndex ((p : Int) + ents.length))).reply
        { type := .appendEntriesResponse, subtype := m.subtype, term := (st.s i).currentTerm,
          success := true, matchIndex := (p : Int) + ents.length, source := i, dest := j } m) := by
  have hnc' : st.hasNoConflict i ((p : Int) + 1) m.entries = true := by
    rw [hents]; exact (hasNoConflict_abs st i C bl p L ents hlog (by omega) hbl hbe).2 hnc
  have hne' : m.entries.isEmpty = false := by
    rw [hents]; cases ents with
    | nil => exact absurd rfl hne
    | cons _ _ => simp [logAbs]
  have hle : (p : Int) + (m.entries.length : Int) ≤ ((st.s i).log.length : Int) := by
    rw [hents, hlog, logAbs_length, logAbs_length]; omega
  have hml : (m.entries.length : Int) = ents.length := by rw [hents, logAbs_length]
  have hc' : ¬ ((p : Int) + 1 ≤ (st.s i).commitIndex) := by omega
  have hsub' : (m.subtype == "heartbeat") = false := by simp [hsub]
  unfold Etcdraft.State.appendEntriesAlreadyDone
  have hle2 : (p : Int) + ents.length ≤ (st.s i).log.length := by rw [← hml]; exact hle
  have hgt : (p : Int) + 1 > (st.s i).commitIndex := hc
  simp only [hne', hnc', hc', hgt, hprev, hsub', hml, hle2, decide_true, decide_false, Bool.not_false,
    Bool.false_or, Bool.and_self, Bool.not_true, Bool.false_eq_true, ↓reduceIte]

/-- `findConflict` is the index of the first entry the log does not match (as `StepRInv`'s
`plogFindConflict_first`, which this module does not import). -/
theorem findConflict_first (b : entryID) (es : List EntryM) :
    ∀ (ents : List EntryM) (d : Nat) (e : EntryM), ents[d]? = some e →
    ¬ PlogMatches b es (entId e) →
    (∀ (j : Nat) (e' : EntryM), j < d → ents[j]? = some e' → PlogMatches b es (entId e')) →
    plogFindConflict b es ents = e.Index' := by
  intro ents
  induction ents with
  | nil => intro d e hd; simp at hd
  | cons a ents ih =>
    intro d e hd hnm hbef
    cases d with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hd
      subst hd
      simp only [plogFindConflict, ite_eq_right hnm]
    | succ d =>
      have ha := hbef 0 a (by omega) rfl
      simp only [plogFindConflict, ite_eq_left ha]
      exact ih d e (by simpa using hd) hnm
        (fun j e' hj he' => hbef (j + 1) e' (by omega) (by simpa using he'))

/-- **Raft's `maybeAppend` on an uncompacted log, as the specification's steps** (a batch after
index `p`, its entries at `p + 1`, ...): either no entry conflicts (the log unchanged, the batch
all in it), or the first conflict is the batch's `d`-th entry, at index `p + d + 1` within one past
the log's end; every prefix of the log longer than `p + d` conflicts with the batch, the prefix
of length `p + d` does not, and the new log is that prefix and the batch from `d` on. -/
theorem maybeAppend_spec (es ents es' : List EntryM) (p : Nat) (lt lastnewi : w64)
    (hwf : ∀ (k : Nat) (e : EntryM), ents[k]? = some e → uint.Z e.Index' = (p : Int) + k + 1)
    (hp : p < 2 ^ 64) (hnw : (p : Int) + ents.length + 1 < 2 ^ 64)
    (happ : plogMaybeAppend (entryID.mk (W64 0) (W64 0)) es (entryID.mk lt (W64 p)) ents = some (lastnewi, es')) :
    p ≤ es.length ∧ uint.Z lastnewi = (p : Int) + ents.length ∧
    ( (es' = es ∧ p + ents.length ≤ es.length ∧
        ∀ k e, ents[k]? = some e → p + k < es.length → (es[p + k]?).map EntryM.Term' = some e.Term')
    ∨ (∃ d, d < ents.length ∧ p + d ≤ es.length ∧ es' = es.take (p + d) ++ ents.drop d ∧
        plogFindConflict (entryID.mk (W64 0) (W64 0)) es ents ≠ W64 0 ∧
        uint.Z (plogFindConflict (entryID.mk (W64 0) (W64 0)) es ents) = (p : Int) + d + 1 ∧
        (∀ k e, ents[k]? = some e → p + k < p + d →
          ((es.take (p + d))[p + k]?).map EntryM.Term' = some e.Term') ∧
        (∀ n, p + d < n → n ≤ es.length → ¬ ∀ k e, ents[k]? = some e → p + k < n →
          ((es.take n)[p + k]?).map EntryM.Term' = some e.Term')) ) := by
  have hpz : uint.Z (W64 p) = p := by word
  have hwf' : PlogWf (entryID.mk lt (W64 p)) ents := by
    intro k e he; have := hwf k e he; simp only [hpz]; push_cast; omega
  have hnw' : uint.Z (entryID.mk lt (W64 p)).index' + (ents.length : Int) + 1 < 2 ^ 64 := by
    simp only [hpz]; exact hnw
  obtain ⟨hm, hlast, hcase⟩ := plogMaybeAppend_inv _ _ _ _ _ _ hwf' hnw' happ
  have hpl : p ≤ es.length := by
    have := (plogTermAt_some_range _ _ _ _ hm).2
    simp only [plogLastIndexZ, hpz] at this
    have h0 : uint.Z (W64 0) = 0 := rfl
    rw [h0] at this; omega
  simp only [hpz] at hlast
  have hmatch : ∀ k e, ents[k]? = some e →
      (PlogMatches (entryID.mk (W64 0) (W64 0)) es (entId e) ↔ es[p + k]?.map EntryM.Term' = some e.Term') := by
    intro k e he; exact plogMatches_base0 es e (p + k) (by rw [hwf k e he]; push_cast; omega)
  refine ⟨hpl, hlast, ?_⟩
  rcases hcase with ⟨hes, hall⟩ | ⟨d, e, hd, hnm, hbef, hei, hend, rfl⟩
  · left
    refine ⟨hes, ?_, fun k e he _ => (hmatch k e he).1 (hall k e he)⟩
    cases hents : ents.getLast? with
    | none => rw [List.getLast?_eq_none_iff.1 hents]; simp; exact hpl
    | some x =>
      obtain ⟨l', hl'⟩ := List.getLast?_eq_some_iff.1 hents
      have hx : ents[l'.length]? = some x := by rw [hl']; simp
      have := (hmatch _ x hx).1 (hall _ x hx)
      have hlt : p + l'.length < es.length := by
        cases hh : es[p + l'.length]? with
        | none => rw [hh] at this; cases this
        | some _ => exact (List.getElem?_eq_some_iff.1 hh).1
      rw [hl']; simp; omega
  · right
    have hdl : d < ents.length := (List.getElem?_eq_some_iff.1 hd).1
    have h0 : uint.Z (W64 0) = 0 := rfl
    simp only [hpz] at hei
    simp only [plogLastIndexZ, h0] at hend
    have hfc := findConflict_first _ es ents d e hd hnm hbef
    refine ⟨d, hdl, by omega, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [h0]; congr 2; omega
    · rw [hfc]; intro hz; rw [hz] at hei; rw [h0] at hei; omega
    · rw [hfc, hei]
    · intro k e' he' hk
      rw [List.getElem?_take_of_lt (by omega)]
      exact (hmatch k e' he').1 (hbef k e' (by omega) he')
    · intro n hn hnl hall
      apply hnm
      rw [hmatch d e hd]
      have := hall d e hd hn
      rwa [List.getElem?_take_of_lt hn] at this

/-- Sending changes only the outbox. -/
theorem sim_psendMsgs (C : List w64) (bl : Nat) (s : PState) (a : Etcdraft.Server) (ms : List Msg)
    (hR : SimServerR C bl s a) : SimServerR C bl (psendMsgs s ms) a := hR

/-- After the truncation at `p + d` and the append, the log has the whole batch. -/
theorem truncAppend_has (es ents : List EntryM) (p d : Nat) (hpd : p + d ≤ es.length)
    (hbef : ∀ k e, ents[k]? = some e → p + k < p + d →
      ((es.take (p + d))[p + k]?).map EntryM.Term' = some e.Term') :
    ∀ k e, ents[k]? = some e → p + k < (es.take (p + d) ++ ents.drop d).length →
      ((es.take (p + d) ++ ents.drop d)[p + k]?).map EntryM.Term' = some e.Term' := by
  intro k e he _
  rw [List.getElem?_append]
  simp only [List.length_take, Nat.min_eq_left hpd]
  split
  · rename_i hk
    have := hbef k e he hk
    rwa [List.getElem?_take_of_lt hk] at this ⊢
  · rename_i hk
    rw [List.getElem?_drop]
    have : d + (p + k - (p + d)) = k := by omega
    rw [this, he]; rfl

/-- **An append request accepted at a follower** (the rule `appAccept`, its log from
`plogMaybeAppend`): the specification's server after the receive line (the truncations, the append,
`AppendEntriesAlreadyDone`'s commit; the leader adopted). -/
theorem sim_appAccept (C : List w64) (bl : Nat) (s : PState) (a : Etcdraft.Server) (src mc lastnewi : w64)
    (es' : List EntryM) (hR : SimServerR C bl s a) (hfol : a.state = Etcdraft.follower) :
    SimServerR C bl
      { padoptLeader s src with
          log := es'
          commit := plogCommitTo s.commit (if uint.Z mc < uint.Z lastnewi then mc else lastnewi) }
      { a with
          log := logAbs C bl 1 es'
          lead := idAbs src
          commitIndex := max a.commitIndex (min (uint.Z mc) (uint.Z lastnewi)) } := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := hR
  have hrole : s.role = .follower := by
    cases hr : s.role <;> rw [hr, hfol] at h2 <;>
      first | rfl | (simp [roleAbs, Etcdraft.follower, Etcdraft.candidate, Etcdraft.leader] at h2)
  refine ⟨h1, ?_, h3, rfl, h5, rfl, ?_, h8, h9, ?_, ?_⟩
  · simp only [padoptLeader]; rw [h2, hrole]
  · simp only [plogCommitTo]; rw [h7]
    repeat' split
    all_goals omega
  · intro h; simp [padoptLeader] at h
  · intro h; simp [padoptLeader] at h

/-- **An append request's `logOk` is raft's `matchTerm` of its previous entry**, on an uncompacted
log (a request after index 0 carries term 0, as every leader's does: `term(0) = 0`). -/
theorem appLogOk_abs (C : List w64) (bl : Nat) (es : List EntryM) (p : Nat) (lt : w64)
    (hbl : BootTerms bl 1 es) (h0 : p = 0 → lt = W64 0) (hp : p < 2 ^ 64) :
    or ((p : Int) == 0) (decide ((p : Int) > 0) && decide ((p : Int) ≤ (logAbs C bl 1 es).length) &&
      some (uint.Z lt) == ((logAbs C bl 1 es)[((p : Int) - 1).toNat]?).map Etcdraft.Entry.term) =
      decide (PlogMatches (entryID.mk (W64 0) (W64 0)) es (entryID.mk lt (W64 p))) := by
  have hpz : uint.Z (W64 p) = p := by word
  rw [logAbs_length]
  by_cases hpz0 : p = 0
  · subst hpz0
    have := h0 rfl; subst this
    have : PlogMatches (entryID.mk (W64 0) (W64 0)) es (entryID.mk (W64 0) (W64 0)) := by
      unfold PlogMatches; exact plogTermAt_base _ _
    rw [show (((0 : Nat) : Int) == 0) = true from rfl, Bool.true_or]
    exact (decide_eq_true this).symm
  · have hp0 : ((p : Int) == 0) = false := by simp; omega
    have hpm : PlogMatches (entryID.mk (W64 0) (W64 0)) es (entryID.mk lt (W64 p)) ↔
        es[p - 1]?.map EntryM.Term' = some lt := by
      unfold PlogMatches
      simp only
      rw [plogTermAt_base0 es _ (by omega)]
      have : uint.nat (W64 p) - 1 = p - 1 := by word
      rw [this]
    have hidx : ((p : Int) - 1).toNat = p - 1 := by omega
    rw [hp0, Bool.false_or, hidx, logAbs_getElem?]
    apply Bool.eq_iff_iff.2
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, hpm]
    constructor
    · rintro ⟨⟨-, hle⟩, h⟩
      obtain ⟨x, hx⟩ : ∃ x, es[p - 1]? = some x := ⟨es[p - 1], List.getElem?_eq_getElem (by omega)⟩
      rw [hx] at h ⊢
      simp only [Option.map_some, Option.some.injEq] at h ⊢
      rw [entAbs_term C bl _ x (fun hb => hbl (p - 1) x (by omega) hx)] at h
      exact (uint_Z_inj.mp h).symm
    · intro h
      obtain ⟨x, hx⟩ : ∃ x, es[p - 1]? = some x := by
        cases hh : es[p - 1]? with
        | none => rw [hh] at h; cases h
        | some x => exact ⟨x, rfl⟩
      have hlt : p - 1 < es.length := (List.getElem?_eq_some_iff.1 hx).1
      rw [hx] at h ⊢
      simp only [Option.map_some, Option.some.injEq] at h ⊢
      refine ⟨⟨by omega, by omega⟩, ?_⟩
      rw [entAbs_term C bl _ x (fun hb => hbl (p - 1) x (by omega) hx), h]

/-- **A non-leader adopts the sender of an append request or heartbeat of its term as leader**
(`becomeFollower(m.Term, m.From)` at a candidate, `r.lead = m.From` at a follower): the
specification's `ReturnToFollowerState` (at a candidate) and the handler's `lead' = j`. -/
theorem sim_adoptLeader (C : List w64) (bl : Nat) (s : PState) (a : Etcdraft.Server) (src : w64)
    (hR : SimServerR C bl s a) :
    SimServerR C bl (padoptLeader s src) { a with state := Etcdraft.follower, lead := idAbs src } := by
  obtain ⟨h1, -, h3, -, h5, h6, h7, h8, h9, -, -⟩ := hR
  refine ⟨h1, rfl, h3, rfl, h5, h6, h7, h8, h9, ?_, ?_⟩
  · intro h; simp [padoptLeader] at h
  · intro h; simp [padoptLeader] at h

/-- **`commitTo`** (raft's `raftLog.commitTo`, the specification's `CommitTo`): both take the
maximum. -/
theorem sim_commitTo (C : List w64) (bl : Nat) (s : PState) (a : Etcdraft.Server) (c : w64)
    (hR : SimServerR C bl s a) :
    SimServerR C bl { s with commit := plogCommitTo s.commit c }
      { a with commitIndex := max a.commitIndex (uint.Z c) } := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := hR
  refine ⟨h1, h2, h3, h4, h5, h6, ?_, h8, h9, h10, h11⟩
  simp only [plogCommitTo]; rw [h7]
  split <;> omega

/-- **A successful append response at a leader** (the rule `appResp`: `MaybeUpdate` of the
sender's `Match`): the specification's `HandleAppendEntriesResponse` (its `matchIndex[j]` the
maximum of the old and the response's). -/
theorem sim_appResp (C : List w64) (bl : Nat) (s : PState) (a : Etcdraft.Server) (src idx x : w64)
    (hR : SimServerR C bl s a) (hx : s.matched !! src = some x) :
    SimServerR C bl
      { s with matched := <[src := (if uint.Z x < uint.Z idx then idx else x)]> s.matched }
      { a with matchIndex := fun k =>
          if k = idAbs src then max (a.matchIndex (idAbs src)) (uint.Z idx) else a.matchIndex k } := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := hR
  refine ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, ?_⟩
  intro hl j hj
  have hold := h11 hl
  simp only
  by_cases hjs : j = src
  · subst hjs
    simp only [↓reduceIte, GMap.lookup_insert, Option.getD_some]
    rw [hold j hj, hx, Option.getD_some]
    split <;> omega
  · have hne : idAbs j ≠ idAbs src := fun e => hjs (idAbs_inj.1 e)
    simp only [hne, ↓reduceIte]
    rw [GMap.lookup_insert_ne _ _ (Ne.symm hjs), hold j hj]

/-! ### Quorums -/

theorem setIds_mk_perm (l : List Etcdraft.ID) (h : l.Nodup) : (Etcdraft.SetIds.mk l).Perm l := by
  apply (List.perm_ext_iff_of_nodup ?_ h).2
  · intro x; exact setIds_mk_mem l x
  · exact (setIds_mk_sorted l).imp (fun h => Nat.ne_of_lt h)

theorem confAbs_perm (C : List w64) (h : C.Nodup) : (confAbs C).Perm (C.map idAbs) :=
  setIds_mk_perm _ (h.map (f := idAbs) (fun _ _ hab e => hab (idAbs_inj.1 e)))

theorem confAbs_length (C : List w64) (h : C.Nodup) : (confAbs C).length = C.length := by
  rw [(confAbs_perm C h).length_eq, List.length_map]

theorem confAbs_filter_length (C : List w64) (h : C.Nodup) (P : Etcdraft.ID → Bool) :
    ((confAbs C).filter P).length = (C.filter (fun j => P (idAbs j))).length := by
  rw [((confAbs_perm C h).filter P).length_eq, List.filter_map, List.length_map]
  rfl

/-- The specification's `isQuorum` of a part of the bootstrap configuration: a majority. -/
theorem isQuorum_filter_confAbs (C : List w64) (h : C.Nodup) (P : Etcdraft.ID → Bool) :
    Etcdraft.isQuorum ((confAbs C).filter P) (confAbs C) =
      decide ((C.filter (fun j => P (idAbs j))).length * 2 > C.length) := by
  unfold Etcdraft.isQuorum Etcdraft.SetIds.subset
  rw [confAbs_filter_length C h, confAbs_length C h]
  have : ((confAbs C).filter P).all (fun id => (confAbs C).contains id) = true := by
    rw [List.all_eq_true]; intro x hx
    exact List.elem_iff.2 (List.mem_filter.1 hx).1
  rw [this, Bool.true_and]

/-- `AdvanceCommitIndex`'s `maxAgree` (a fold over the log's indices) is the largest index at most
`L` that `q` holds at, or 0. -/
theorem maxAgree_spec (q : Nat → Bool) (L : Nat) :
    let M := (List.range L).foldl (fun acc n => if q (n + 1) then n + 1 else acc) 0
    (M = 0 ∨ (1 ≤ M ∧ M ≤ L ∧ q M = true)) ∧ ∀ k, M < k → k ≤ L → q k = false := by
  induction L with
  | zero => simp; intro k h1 h2; omega
  | succ L ih =>
    simp only [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil] at ih ⊢
    obtain ⟨h1, h2⟩ := ih
    by_cases hq : q (L + 1) = true
    · simp only [hq, ↓reduceIte]
      refine ⟨Or.inr ⟨by omega, Nat.le_refl _, trivial⟩, fun k hk hk' => by omega⟩
    · simp only [hq, Bool.false_eq_true, ↓reduceIte]
      refine ⟨?_, fun k hk hk' => ?_⟩
      · rcases h1 with h | ⟨a, b, c⟩
        · exact Or.inl h
        · exact Or.inr ⟨a, by omega, c⟩
      · by_cases hkl : k = L + 1
        · subst hkl; simpa using hq
        · exact h2 k hk (by omega)

/-- ... so it is any index `n ≤ L` that `q` holds at and at no larger index up to `L`. -/
theorem maxAgree_eq (q : Nat → Bool) (L n : Nat) (hn1 : 1 ≤ n) (hnL : n ≤ L) (hq : q n = true)
    (hmax : ∀ k, n < k → k ≤ L → q k = false) :
    (List.range L).foldl (fun acc n => if q (n + 1) then n + 1 else acc) 0 = n := by
  obtain ⟨h1, h2⟩ := maxAgree_spec q L
  generalize hM : (List.range L).foldl (fun acc n => if q (n + 1) then n + 1 else acc) 0 = M at h1 h2
  rcases Nat.lt_trichotomy M n with h | h | h
  · have := h2 n h hnL; rw [hq] at this; cases this
  · exact h
  · rcases h1 with h0 | ⟨_, hML, hqM⟩
    · omega
    · have := hmax M h hML; rw [hqM] at this; cases this

/-- Raft's quorum of the voters acknowledging index `n > 0` (`ackedBy`), as a count over the
bootstrap configuration. -/
theorem isQuorum_ackedBy (C : List w64) (hnd : C.Nodup) (s : PState) (n : w64) (hn : 0 < uint.Z n) :
    IsQuorum (GMap.listToSet C) (ackedBy s n) ↔
      C.length < 2 * (C.filter (fun j => decide (uint.Z n ≤ uint.Z (matchOf s j)))).length := by
  unfold IsQuorum
  have hset : ackedBy s n ∩ GMap.listToSet C =
      GMap.listToSet (C.filter (fun j => decide (uint.Z n ≤ uint.Z (matchOf s j)))) := by
    apply GMap.set_eq; intro j
    rw [GMap.elem_of_intersection, GMap.elem_of_list_to_set, GMap.elem_of_list_to_set, List.mem_filter,
      ackedBy, GMap.elem_of_dom, GMap.lookup_filter, decide_eq_true_iff]
    unfold matchOf
    constructor
    · rintro ⟨⟨v, hv⟩, hj⟩
      refine ⟨hj, ?_⟩
      cases hm : s.matched !! j with
      | none => rw [hm] at hv; cases hv
      | some x =>
        rw [hm] at hv
        simp only [Option.filter_some, decide_eq_true_eq] at hv
        split at hv
        · rename_i h; simpa using h
        · cases hv
    · rintro ⟨hj, hle⟩
      refine ⟨?_, hj⟩
      cases hm : s.matched !! j with
      | none =>
        rw [hm] at hle; simp only [Option.getD_none] at hle
        have : uint.Z (W64 0) = 0 := rfl
        omega
      | some x =>
        rw [hm] at hle; simp only [Option.getD_some] at hle
        exact ⟨x, by simp only [Option.filter_some, decide_eq_true_eq]; simp only [hle, ↓reduceIte]⟩
  rw [hset, GMap.size_list_to_set _ hnd, GMap.size_list_to_set _ (hnd.filter _)]

end TraceSim

end EtcdGrove
end Perennial
