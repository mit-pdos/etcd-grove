/-
Lean-first (no Rocq counterpart). #33 S3b W7 (2026-11-23): the pure laws of `check.go`'s proofs
(`Checker.Next`, `Run`): `Checker.next` and `gcLoop` taken apart, the budget carried through
`next` (from `StepWithin`, `GCWithin`), and a checker with a verdict left as it is by the rest of
the stream.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Within.Laws

@[expose] public section

namespace Perennial
namespace EtcdGrove
namespace AntCheck
namespace CheckLaws

set_option linter.unusedSimpArgs false

/-- `violated` is empty only where `viol` is. -/
theorem viol_nil_of_violated_nil {s : State} (h : violated s = []) : s.viol = [] := by
  unfold violated at h
  split at h
  · cases h
  · split at h
    · cases h
    · exact h

/-- A checker with a verdict takes no report. -/
theorem next_of_done {c : Checker} (ev : Event) (h : c.done = true) : c.next ev = .ok c := by
  unfold Checker.next; simp [h]

/-- A checker with a verdict is left as it is by the rest of the stream. -/
theorem foldlM_next_of_done {c : Checker} (h : c.done = true) :
    ∀ evs : List Event, evs.foldlM (fun c ev => c.next ev) c = .ok c
  | [] => rfl
  | ev :: evs => by
    rw [List.foldlM_cons, next_of_done ev h]
    exact foldlM_next_of_done h evs

/-- One iteration of `gcLoop`, where it evaluates: some fuel left, `GCDue` evaluated, and either
not due (the state is the result) or `GC` evaluated, its state checked, the loop going on. -/
theorem gcLoop_ok {k : Nat} {s : State} {r : State × Option Verdict} (h : gcLoop k s = .ok r) :
    ∃ k', k = k' + 1 ∧ ∃ due, s.gcDue = .ok due ∧
      (due = false → r = (s, none)) ∧
      (due = true → ∃ s1, s.gc = .ok s1 ∧
        (violated s1 ≠ [] → r = (s1, some { kind := .violated, k := s1.i - 1, names := violated s1 })) ∧
        (violated s1 = [] → gcLoop k' s1 = .ok r)) := by
  cases k with
  | zero => unfold gcLoop evalError at h; cases h
  | succ k' =>
    refine ⟨k', rfl, ?_⟩
    unfold gcLoop at h
    cases hd : s.gcDue with
    | error e => rw [hd] at h; cases h
    | ok due =>
      refine ⟨due, rfl, ?_, ?_⟩
      · intro hf; subst hf; rw [hd] at h
        simp only [ok_bind, Bool.not_false, ↓reduceIte, pure_ok, Except.ok.injEq] at h
        exact h.symm
      · intro ht; subst ht; rw [hd] at h
        simp only [ok_bind, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
        cases hg : s.gc with
        | error e => rw [hg] at h; cases h
        | ok s1 =>
          rw [hg] at h
          simp only [ok_bind] at h
          refine ⟨s1, rfl, ?_, ?_⟩
          · intro hv
            rw [ite_eq_left (by simpa using hv)] at h
            simp only [pure_ok, Except.ok.injEq] at h
            exact h.symm
          · intro hv
            rw [ite_eq_right (by simp [hv])] at h
            exact h

/-- `Checker.next` on a checker without a verdict, where it evaluates: `gcLoop`'s result, then
(no verdict from it) `Step`'s, and the checker each case gives. -/
theorem next_ok {c c' : Checker} {ev : Event} (hd : c.done = false) (h : c.next ev = .ok c') :
    ∃ s vo, gcLoop (gcFuel c.state) c.state = .ok (s, vo) ∧
      (∀ v, vo = some v → c' = { state := s, done := true, verdict := v }) ∧
      (vo = none → ∃ o, s.step ev = .ok o ∧
        (o = none → c' = { state := s, done := true, verdict := { kind := .rejected, k := s.i } }) ∧
        (∀ ns, o = some ns →
          (violated ns ≠ [] →
            c' = { state := ns, done := true, verdict := { kind := .violated, k := s.i, names := violated ns } }) ∧
          (violated ns = [] → c' = { c with state := ns }))) := by
  unfold Checker.next at h
  simp only [hd, Bool.false_eq_true, ↓reduceIte] at h
  cases hg : gcLoop (gcFuel c.state) c.state with
  | error e => rw [hg] at h; cases h
  | ok r =>
    obtain ⟨s, vo⟩ := r
    rw [hg] at h
    simp only [ok_bind] at h
    refine ⟨s, vo, rfl, ?_, ?_⟩
    · intro v hv; subst hv
      simp only [pure_ok, Except.ok.injEq] at h
      exact h.symm
    · intro hv; subst hv
      simp only at h
      cases hs : s.step ev with
      | error e => rw [hs] at h; cases h
      | ok o =>
        rw [hs] at h
        simp only [ok_bind] at h
        refine ⟨o, rfl, ?_, ?_⟩
        · intro ho; subst ho
          simp only [pure_ok, Except.ok.injEq] at h
          exact h.symm
        · intro ns hns; subst hns
          refine ⟨fun hv => ?_, fun hv => ?_⟩
          · simp only at h
            rw [ite_eq_left (by simpa using hv)] at h
            simp only [pure_ok, Except.ok.injEq] at h
            exact h.symm
          · simp only at h
            rw [ite_eq_right (by simp [hv])] at h
            simp only [pure_ok, Except.ok.injEq] at h
            rw [hd]; exact h.symm

/-- `gcLoop` keeps the state within budget (`GC` does: `GCWithin`). -/
theorem gcLoop_within_of (gc_within : GCWithin) :
    ∀ (k : Nat) (s s' : State) (vo : Option Verdict) (b E : Nat),
      gcLoop k s = .ok (s', vo) → s.Within b E → s'.Within b E := by
  intro k
  induction k with
  | zero => intro s s' vo b E h; unfold gcLoop evalError at h; cases h
  | succ k ih =>
    intro s s' vo b E h hW
    obtain ⟨k', hk, due, -, hf, ht⟩ := gcLoop_ok h
    cases hk
    cases due
    · cases hf rfl; exact hW
    · obtain ⟨s1, hg, hv, hn⟩ := ht rfl
      have hW1 := gc_within s s1 b E hW hg
      by_cases h0 : violated s1 = []
      · exact ih s1 s' vo b E (hn h0) hW1
      · cases hv h0; exact hW1

/-- **`next` keeps the budget** (`Run`'s invariant, from `StepWithin` and `GCWithin`): a checker
within `b` that takes report `ev` without reaching a verdict is within `b + ev.weight`. -/
theorem next_within_of (step_within : StepWithin) (gc_within : GCWithin)
    {c c' : Checker} {ev : Event} {b E : Nat} (hd : c.done = false) (hW : c.state.Within b E)
    (hNO : ev.NumsOk) (hCh : ev.ChgOk E) (hb : ((b + ev.weight : Nat) : Int) < numBound)
    (h : c.next ev = .ok c') (hd' : c'.done = false) : c'.state.Within (b + ev.weight) E := by
  obtain ⟨s, vo, hg, hsome, hnone⟩ := next_ok hd h
  have hWs := gcLoop_within_of gc_within _ _ _ _ _ _ hg hW
  cases vo with
  | some v => rw [hsome v rfl] at hd'; cases hd'
  | none =>
    obtain ⟨o, hs, hno, hso⟩ := hnone rfl
    cases o with
    | none => rw [hno rfl] at hd'; cases hd'
    | some ns =>
      obtain ⟨hv1, hv0⟩ := hso ns rfl
      by_cases h0 : violated ns = []
      · rw [hv0 h0]
        exact step_within s ev b E ns hWs hNO hCh hb hs (viol_nil_of_violated_nil h0)
      · rw [hv1 h0] at hd'; cases hd'

/-- `GC` keeps the configuration. -/
theorem gc_cfg {s s' : State} (h : s.gc = .ok s') : s'.cfg = s.cfg := by
  unfold State.gc at h
  obtain ⟨g, -, h⟩ := bind_ok h
  obtain ⟨o, -, h⟩ := bind_ok h
  simp only [pure_ok, Except.ok.injEq] at h
  subst h; rfl

/-- `gcLoop` keeps the configuration. -/
theorem gcLoop_cfg : ∀ (k : Nat) (s s' : State) (vo : Option Verdict),
    gcLoop k s = .ok (s', vo) → s'.cfg = s.cfg := by
  intro k
  induction k with
  | zero => intro s s' vo h; unfold gcLoop evalError at h; cases h
  | succ k ih =>
    intro s s' vo h
    obtain ⟨k', hk, due, -, hf, ht⟩ := gcLoop_ok h
    cases hk
    cases due
    · cases hf rfl; rfl
    · obtain ⟨s1, hg, hv, hn⟩ := ht rfl
      by_cases h0 : violated s1 = []
      · rw [ih s1 s' vo (hn h0), gc_cfg hg]
      · cases hv h0; exact gc_cfg hg

end CheckLaws
end AntCheck
end EtcdGrove
end Perennial
