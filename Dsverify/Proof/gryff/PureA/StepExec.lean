/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/PureA/StepExec.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

Unit A1, internal (A1a): the step case `inv_exec` of `inv_step` (`Inv.lean`): the execution turns a
COMMITTED copy EXECUTED and sends an `ExecuteOverwrite` to itself (`inv_sim`).
-/
module

public import Dsverify.Proof.gryff.PureA.StepSim

@[expose] public section

set_option linter.unusedSectionVars false

namespace Perennial.gryff.pureA

open Perennial Perennial.gryff.model Perennial.gryff.pure Perennial.gryff.kahn

theorem simFrame_setInst' {s t : RState} {q i : w32} {cp cp' : Copy} (ht : SimFrame s t)
    (hst : t.inst = s.inst) (hc : s.inst q i = some cp) (hs : CopySim cp cp') :
    SimFrame s (t.setInst q i cp') := by
  refine ⟨ht.1, ht.2.1, fun q' i' => ?_⟩
  rw [setInst_inst]
  split
  · rename_i e; obtain ⟨rfl, rfl⟩ := e; rw [hc]; exact hs
  · rw [hst]; exact OSim.refl _

theorem stepExec_sim {s s' : RState} {q i : w32} {o : List Out} (h : stepExec s q i = .ok (s', o)) :
    SimFrame s s' ∧ QuietO o := by
  unfold stepExec at h; peel h
  all_goals (
    cases h
    constructor
    · apply simFrame_setInst' (SimFrame.of_frame ⟨rfl, rfl, rfl⟩) rfl asm
      exact ⟨rfl, rfl, rfl, Or.inr ⟨Classical.not_not.mp asm, rfl⟩, rfl⟩
    first
    | exact quietO_nil
    | exact quietO_single (sendTo_send asm) rfl)

theorem inv_exec {c c1 : Cfg gNet} {G : GG} {a : Fin 3} {q0 i0 : w32} {s' : RState}
    {o : List Out} (I : CInv c G) (hp : Post c a (.exec q0 i0) s' o c1)
    (h : stepR a (c.st a) (.exec q0 i0) = .ok (s', o)) : StepInv c c1 G :=
  inv_sim I hp (stepExec_sim h).1 (stepExec_sim h).2

end Perennial.gryff.pureA
