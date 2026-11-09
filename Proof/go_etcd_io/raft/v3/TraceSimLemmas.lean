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

end TraceSim

end EtcdGrove
end Perennial
