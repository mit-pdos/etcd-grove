/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/PureA/IntfRun.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

Unit AI, internal: **the interference invariant along a run** (`intf_reach`), and D1 for committed
values: `interf` in `GryffProof/Pure/Agree.lean` takes `intf_reach` and `interf_vals`.
-/
module

public import Dsverify.Proof.gryff.PureA.IntfStep
public import Dsverify.Proof.gryff.PureL.Run

@[expose] public section

set_option linter.unusedSectionVars false

namespace Perennial.gryff.pureA.AI

open Perennial Perennial.gryff.model Perennial.gryff.pure Perennial.gryff.kahn Perennial.gryff.pureA

/-- Every reachable configuration has ghosts satisfying `IInv`. -/
theorem intf_reach {l : List Label} {c : Cfg gNet} (h : GRun (Cfg.init gNet) l c) :
    ∃ κ rc dg, IInv c κ rc dg :=
  intf_run inv_init intf_init h

end Perennial.gryff.pureA.AI
