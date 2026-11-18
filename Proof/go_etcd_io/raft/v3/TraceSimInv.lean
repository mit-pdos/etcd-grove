/-
Lean-first (no Rocq counterpart). Trace-check's layer B (2026-11-09): the invariants of
`Traceetcdraft.cfg` as facts about a state's servers (`InvFacts`), which give `violated = none`
(no violation and no evaluation error). Raft's side establishes the facts through `R`
(`notes/trace-validation-sim.md`, "The invariants").
-/
module

public import Proof.go_etcd_io.raft.v3.TraceSimLemmas

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

namespace TraceSim

open Etcdraft

/-- A server's committed prefix. -/
def committedL (st : State) (i : ID) : List Entry := (st.s i).log.take (st.s i).commitIndex.toNat

/-- Every server's commit index within its log. -/
def CommitOk (st : State) : Prop :=
  ∀ i ∈ st.server, 0 ≤ (st.s i).commitIndex ∧ (st.s i).commitIndex ≤ (st.s i).log.length

theorem committed_eq (st : State) (i : ID) (h0 : 0 ≤ (st.s i).commitIndex)
    (h1 : (st.s i).commitIndex ≤ (st.s i).log.length) : st.committed i = .ok (committedL st i) := by
  unfold State.committed committedL subSeqM subSeq
  by_cases hc : (1 : Int) > (st.s i).commitIndex
  · have : (st.s i).commitIndex.toNat = 0 := by omega
    simp only [hc, ↓reduceIte, this, List.take_zero]; rfl
  · have h2 : ¬ ((1 : Int) < 1 ∨ (st.s i).commitIndex > (st.s i).log.length) := by omega
    simp only [hc, h2, ↓reduceIte]
    have : (st.s i).commitIndex.toNat - (1 : Int).toNat + 1 = (st.s i).commitIndex.toNat := by omega
    simp only [Int.toNat_one, Nat.sub_self, List.drop_zero]
    rw [show (st.s i).commitIndex.toNat - 1 + 1 = (st.s i).commitIndex.toNat by omega]; rfl

/-- **The invariants as facts**: each of `Traceetcdraft.cfg`'s, with `Committed(i)` the committed
prefix (the commit indices within the logs: `Committed` evaluates), and `LeaderCompletenessInv`'s
`log[l][idx]` within the leader's log where it is read. -/
structure InvFacts (st : State) : Prop where
  commit : CommitOk st
  logInv : ∀ i ∈ st.server, ∀ j ∈ st.server,
    (or (isPrefix (committedL st i) (committedL st j)) (isPrefix (committedL st j) (committedL st i))) = true
  oneLeader : st.moreThanOneLeaderInv = true
  electionSafety : st.electionSafetyInv = true
  logMatching : st.logMatchingInv = true
  quorumLog : ∀ i ∈ st.server,
    isQuorum ((st.getConfig i).filter (fun j => or (!st.server.contains j) (!isPrefix (committedL st i) (st.s j).log)))
      (st.getConfig i) = false
  leaderCompleteness : ∀ i ∈ st.server, ∀ idx0 < (committedL st i).length, ∀ l ∈ st.currentLeaders,
    (st.s l).currentTerm > (((st.s i).log[idx0]?).getD default).term →
    (st.s l).currentTerm ≥ (st.s i).currentTerm →
    (st.s l).log[idx0]? = some (((st.s i).log[idx0]?).getD default)
  durable : st.committedIsDurableInv = true

theorem allM_ok_true {α ε : Type} (f : α → Except ε Bool) :
    ∀ (l : List α), (∀ x ∈ l, f x = .ok true) → l.allM f = .ok true := by
  intro l
  induction l with
  | nil => intro _; rw [List.allM_nil]; rfl
  | cons a l ih =>
    intro h
    rw [List.allM_cons, h a (by simp)]
    simp only [bind, Except.bind, ↓reduceIte]
    exact ih (fun x hx => h x (by simp [hx]))

theorem logInv_ok (st : State) (h : InvFacts st) : st.logInv = .ok true := by
  unfold State.logInv
  apply allM_ok_true; intro i hi
  apply allM_ok_true; intro j hj
  rw [committed_eq st i (h.commit i hi).1 (h.commit i hi).2, committed_eq st j (h.commit j hj).1 (h.commit j hj).2]
  have := h.logInv i hi j hj
  simp only [bind, Except.bind, pure, Except.pure]
  rw [← this]

theorem quorumLogInv_ok (st : State) (h : InvFacts st) : st.quorumLogInv = .ok true := by
  unfold State.quorumLogInv
  apply allM_ok_true; intro i hi
  rw [committed_eq st i (h.commit i hi).1 (h.commit i hi).2]
  have := h.quorumLog i hi
  simp only [bind, Except.bind, pure, Except.pure]
  rw [this]; rfl

theorem leaderCompletenessInv_ok (st : State) (h : InvFacts st) : st.leaderCompletenessInv = .ok true := by
  unfold State.leaderCompletenessInv
  simp only [bind, Except.bind]
  apply allM_ok_true; intro i hi
  rw [committed_eq st i (h.commit i hi).1 (h.commit i hi).2]
  simp only
  apply allM_ok_true; intro idx0 hidx
  rw [List.mem_range] at hidx
  apply allM_ok_true; intro l hl
  have hlc := h.leaderCompleteness i hi idx0 hidx l hl
  split
  · rename_i hc
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
    rw [hlc hc.1 hc.2]
    simp [pure, Except.pure]
  · rfl

/-- **The facts give no violation and no evaluation error.** -/
theorem violated_none (st : State) (h : InvFacts st) : st.violated = .ok none := by
  unfold State.violated invariants
  simp only [List.foldlM_cons, List.foldlM_nil, bind, Except.bind, pure, Except.pure,
    logInv_ok st h, quorumLogInv_ok st h, leaderCompletenessInv_ok st h, h.oneLeader, h.electionSafety,
    h.logMatching, h.durable, ↓reduceIte]

end TraceSim

end EtcdGrove
end Perennial
