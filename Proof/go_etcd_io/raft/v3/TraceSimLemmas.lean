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

end TraceSim

end EtcdGrove
end Perennial
