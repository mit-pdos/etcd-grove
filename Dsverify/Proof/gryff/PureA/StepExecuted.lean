/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/PureA/StepExecuted.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

Unit A1, internal (A1a): the step case `inv_executed` of `inv_step` (`Inv.lean`): `handleExecuted`
changes only the copy's `numReplicasExecuted`/`repliedClient` and answers a client (`inv_sim`).
-/
module

public import Dsverify.Proof.gryff.PureA.StepExec

@[expose] public section

set_option linter.unusedSectionVars false

namespace Perennial.gryff.pureA

open Perennial Perennial.gryff.model Perennial.gryff.pure Perennial.gryff.kahn

theorem copySim_lb {c : Copy} {l l' : LB} (hc : c.lb = some l) (e : lbProj l' = lbProj l) :
    CopySim c { c with lb := some l' } :=
  ⟨rfl, rfl, rfl, Or.inl rfl, by rw [hc]; simp only [Option.map_some, e]⟩

theorem handleExecuted_sim {s s' : RState} {m : ExecutedM} {o : List Out}
    (h : handleExecuted s m = .ok (s', o)) : SimFrame s s' ∧ QuietO o := by
  unfold handleExecuted at h; peel h
  all_goals (
    cases h
    first
    | exact ⟨SimFrame.of_frame ⟨rfl, rfl, rfl⟩, quietO_nil⟩
    | (constructor
       · apply simFrame_setInst' (SimFrame.of_frame ⟨rfl, rfl, rfl⟩) rfl asm
         exact copySim_lb asm (by rfl)
       first
       | exact quietO_nil
       | exact quietO_ext))

theorem inv_executed {c c1 : Cfg gNet} {G : GG} {a : Fin 3} {m : ExecutedM} {s' : RState}
    {o : List Out} (I : CInv c G) (hp : Post c a (.msg (.executed m)) s' o c1)
    (_hm : Msg.executed m ∈ c.inflight a) (h : stepR a (c.st a) (.msg (.executed m)) = .ok (s', o)) :
    StepInv c c1 G :=
  inv_sim I hp (handleExecuted_sim h).1 (handleExecuted_sim h).2

end Perennial.gryff.pureA
