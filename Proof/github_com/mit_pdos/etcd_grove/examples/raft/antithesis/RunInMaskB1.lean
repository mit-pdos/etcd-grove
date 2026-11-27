/-
Lean-first (no Rocq counterpart). #33 parity B1: `runInMask.law` (`HarnessInput.lean`) at B1's
mask `AntSim.mskB1`, the mask the Link instantiates the node inputs' proofs at: a run of the driver
is within `mskB1` (`inMask_b1_of`, `DrainSteps.lean`), its features the scope's (`ModeRun`:
`R.md = scopeMd scope`, within `mskB1.md` by `DrainB1`'s scope bits), its driver modes the mode's
(`ModeRun`: `R.drv = modeDrv mode`, all off by `DrainB1`'s mode bits).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.DrainSteps
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.HarnessInput

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace AntHarness

open Iris Iris.BI go_etcd_io.raft.v3

section pure
variable [GooseExts]

/-- **A run of the driver is within `mskB1`** (`runInMask.law` at `AntSim.mskB1`). -/
theorem runInMask_b1 : runInMask.law AntSim.mskB1 := by
  intro γ evs S V net xnet _ hmr hb1 hrun
  obtain ⟨-, -, -, -, hmd, hdrv⟩ := hmr
  obtain ⟨hb, -, hp, hs, -, hr, hsn, hcc, hfw, has⟩ := hb1
  refine inMask_b1_of ?_ ?_ ?_ ?_ ?_ hrun.2.1
  · rw [hmd]; exact rnLe_scopeMd_b1 _ hfw has hsn hcc
  · rw [hdrv]; exact hb
  · rw [hdrv]; exact hp
  · rw [hdrv]; simp [modeDrv, hs]
  · rw [hdrv]; exact hr

end pure

end AntHarness
end EtcdGrove
end Perennial
