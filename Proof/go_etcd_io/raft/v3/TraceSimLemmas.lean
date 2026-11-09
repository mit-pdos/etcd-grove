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

end TraceSim

end EtcdGrove
end Perennial
