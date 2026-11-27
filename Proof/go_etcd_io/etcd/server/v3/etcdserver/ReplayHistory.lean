/- Interpret a physical run as the term of every log index in its closed interval. -/
module
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.ReplayAppend
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.ReplayJob

@[expose] public section
noncomputable section
namespace Perennial
namespace EtcdGrove
open go_etcd_io.etcd.server.v3.etcdserver

variable [GooseExts]

theorem replayLayout_sublist {rs small : List replayTermRun} (h : replayLayout rs)
    (hs : small.Sublist rs) : replayLayout small :=
  ⟨fun r hr => h.1 r (hs.subset hr), h.2.sublist hs⟩

/-- The interval containing the index is precisely the one found by the Go loop.
The two endpoint comparisons in covers also pass. -/
theorem replay_lookup_interval (rs : List replayTermRun) (r : replayTermRun) (ci t : w64)
    (hs : replayLayout rs) (hr : r ∈ rs) (hc : replayContains r ci t) :
    replayRunCovers rs ci = true ∧ replayRunAt rs ci = some r := by
  obtain ⟨j, hj, he⟩ := List.mem_iff_getElem.mp hr
  have hlen : 0 < rs.length := by omega
  let last := rs.length - 1
  have hl : last < rs.length := by dsimp [last]; omega
  have hhead : rs.head? = some rs[0] := by
    rw [List.head?_eq_getElem?]; exact List.getElem?_eq_getElem hlen
  have hend : rs.getLast? = some rs[last] := by
    rw [List.getLast?_eq_getElem?]; exact List.getElem?_eq_getElem hl
  have hlo : uint.nat rs[0].first' ≤ uint.nat ci := by
    by_cases hz : j = 0
    · subst j; rw [he]; exact hc.1
    · have hlt := hs.2.rel_getElem_of_lt hlen hj (show 0 < j by omega)
      rw [he] at hlt
      exact Nat.le_trans (hs.1 _ (List.getElem_mem hlen)) (Nat.le_trans (Nat.le_of_lt hlt) hc.1)
  have hhi : uint.nat ci ≤ uint.nat rs[last].last' := by
    by_cases hz : j = last
    · subst j; rw [he]; exact hc.2.1
    · have hlt := hs.2.rel_getElem_of_lt hj hl (show j < last by dsimp [last] at *; omega)
      rw [he] at hlt
      exact Nat.le_trans hc.2.1 (Nat.le_trans (Nat.le_of_lt hlt) (hs.1 _ (List.getElem_mem hl)))
  constructor
  · simp only [replayRunCovers, hhead, hend, decide_eq_true_eq]
    constructor <;> word
  · apply List.find?_eq_some_iff_getElem.mpr
    refine ⟨by simpa using hc.2.1, j, hj, he, ?_⟩
    intro i hi
    have hlt := hs.2.rel_getElem_of_lt (Nat.lt_trans hi hj) hj hi
    rw [he] at hlt
    have hprev := Nat.lt_of_lt_of_le hlt hc.1
    simpa using hprev

/-- All pending entries in the durable Raft state have a run with their actual term. -/
def replayHistoryMatches (rs : List replayTermRun) (S : RaftState) (n : Nat) : Prop :=
  replayLayout rs ∧ ∀ (ci t : w64), n < uint.nat ci → plogTermAt S.base S.ents ci = some t →
    ∃ r ∈ rs, replayContains r ci t

theorem replayHistoryMatches_describe (rs : List replayTermRun) (S : RaftState) (n : Nat)
    (h : replayHistoryMatches rs S n) : replayRunsDescribe rs S n := by
  intro ci t hn ht
  obtain ⟨r, hr, hc⟩ := h.2 ci t hn ht
  obtain ⟨hcov, hread⟩ := replay_lookup_interval rs r ci t h.1 hr hc
  exact ⟨hcov, r, hread, hc.2.2⟩

/-- Advancing the apply cursor discards only runs that cannot contain a pending index. -/
theorem replayHistoryMatches_after (rs : List replayTermRun) (S : RaftState)
    (n : Nat) (applied : w64) (hle : n ≤ uint.nat applied) (h : replayHistoryMatches rs S n) :
    replayHistoryMatches (rs.dropWhile (fun r => decide (uint.nat r.last' ≤ uint.nat applied))) S (uint.nat applied) := by
  refine ⟨replayLayout_sublist h.1 (List.dropWhile_sublist _), ?_⟩
  intro ci t hn ht
  obtain ⟨r, hr, hc⟩ := h.2 ci t (Nat.lt_of_le_of_lt hle hn) ht
  refine ⟨r, ?_, hc⟩
  have hkeep : ¬uint.nat r.last' ≤ uint.nat applied := by have := hc.2.1; omega
  clear h
  induction rs with
  | nil => cases hr
  | cons hd tail ih =>
    by_cases hd' : uint.nat hd.last' ≤ uint.nat applied
    · have hne : r ≠ hd := by rintro rfl; exact hkeep hd'
      simp only [List.dropWhile, hd', decide_true, ↓reduceIte]
      exact ih ((List.mem_cons.mp hr).resolve_left hne)
    · simpa [List.dropWhile, hd'] using hr

end EtcdGrove
end Perennial
