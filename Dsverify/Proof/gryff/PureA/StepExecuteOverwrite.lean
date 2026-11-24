/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/PureA/StepExecuteOverwrite.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

Unit A1, internal (A1a): the step case `inv_executeOverwrite` of `inv_step` (`Inv.lean`): the store
overwrite (`Frame`), then `handleExecuted` or an `Executed` notice to the leader (`inv_sim`).
-/
module

public import Dsverify.Proof.gryff.PureA.StepExecuted

@[expose] public section

set_option linter.unusedSectionVars false

namespace Perennial.gryff.pureA

open Perennial Perennial.gryff.model Perennial.gryff.pure Perennial.gryff.kahn

theorem stepExecuteOverwrite_sim {s s' : RState} {m : ExecuteOverwriteM} {o : List Out}
    (h : stepExecuteOverwrite s m = .ok (s', o)) : SimFrame s s' ∧ QuietO o := by
  have hf := overwrite_frame s m.v m.t
  unfold stepExecuteOverwrite at h; peel h
  · have k := handleExecuted_sim h
    exact ⟨(SimFrame.of_frame hf).trans k.1 hf, k.2⟩
  · cases h
    exact ⟨SimFrame.of_frame hf, quietO_single (sendPeer_send asm) rfl⟩

theorem inv_executeOverwrite {c c1 : Cfg gNet} {G : GG} {a : Fin 3} {m : ExecuteOverwriteM}
    {s' : RState} {o : List Out} (I : CInv c G)
    (hp : Post c a (.msg (.executeOverwrite m)) s' o c1)
    (_hm : Msg.executeOverwrite m ∈ c.inflight a)
    (h : stepR a (c.st a) (.msg (.executeOverwrite m)) = .ok (s', o)) : StepInv c c1 G :=
  inv_sim I hp (stepExecuteOverwrite_sim h).1 (stepExecuteOverwrite_sim h).2

end Perennial.gryff.pureA
