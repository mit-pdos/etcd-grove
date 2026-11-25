/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/B/Pure.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

Unit B: pure helpers (the replica's trace run).
-/
module

public import Dsverify.Proof.gryff.Pure.Run

@[expose] public section

set_option linter.unusedSectionVars false

namespace Perennial.gryff.unitB

open model kahn pure

theorem runFrom_append {N : Net} (k : Fin N.n) (s : N.S) (l1 l2 : List N.E) :
    runFrom N k s (l1 ++ l2) =
      (runFrom N k s l1).bind (fun r => (runFrom N k r.1 l2).map (fun r2 => (r2.1, r.2 ++ r2.2))) := by
  induction l1 generalizing s with
  | nil =>
    simp only [List.nil_append, runFrom, Option.bind_some, List.nil_append]
    cases runFrom N k s l2 <;> rfl
  | cons e l ih =>
    simp only [List.cons_append, runFrom]
    cases N.step k s e with
    | none => rfl
    | some p =>
      simp only [ih]
      cases runFrom N k p.1 l with
      | none => rfl
      | some r =>
        simp only [Option.bind_some, Option.map_some, Option.map_map]
        cases runFrom N k r.1 l2 <;> simp [List.append_assoc]

theorem runP_snoc {N : Net} (k : Fin N.n) (t : List N.E) (e : N.E) (s s' : N.S) (o outs : List _)
    (ho : runP N k t = some (s, o)) (hstep : N.step k s e = some (s', outs)) :
    runP N k (t ++ [e]) = some (s', o ++ outs) := by
  unfold runP at ho ⊢
  rw [runFrom_append, ho]
  simp [runFrom, hstep]

/-- A trace that runs: its state after one more `.ok` step is the step's. -/
theorem stOf_snoc (k : Fin 3) (t : List Ev) (e : Ev) (s' : RState) (outs : List Out)
    (h : ∃ o, runP gNet k t = some (stOf k t, o))
    (hs : stepR k (stOf k t) e = .ok (s', outs)) : stOf k (t ++ [e]) = s' := by
  obtain ⟨o, ho⟩ := h
  have hstep : gNet.step k (stOf k t) e = some (s', outs) := by
    show (stepR k (stOf k t) e).toOption = _
    rw [hs]; rfl
  have := runP_snoc (N := gNet) k t e _ _ o outs ho hstep
  unfold stOf
  split
  · rename_i h; have h2 := h.symm.trans this; cases h2; rfl
  · rename_i h; have h2 := h.symm.trans this; cases h2

end Perennial.gryff.unitB
