/- Lean-first (no Rocq counterpart).

# Its top-level statement's premises are satisfiable

`premise_sat%` (`Robustness/PremiseSat.lean`): the statement of `Net/Spec/github_com/mit_pdos/etcd_grove/examples/net/echo/TopLevelRobustness.lean` has premises that hold
together with `Robust`'s antecedents: every machine fresh with no listener, and no connection (`Hconns`). Checked by `etc/premise-witness.py`.
-/
module

public import Net.Spec.github_com.mit_pdos.etcd_grove.examples.net.echo.TopLevelRobustness
public import Robustness.PremiseSat

@[expose] public section

noncomputable section

namespace Perennial
namespace github_com.mit_pdos.etcd_grove.examples.net.echo



open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net
attribute [local instance] netExts netExtsSemantics netExtsInterp netExts_hasNet

open Robustness

theorem echo_crash_robust.premisesSat : premise_sat% echo_crash_robust.spec := by
  intros
  refine ⟨freshState ((default : Net.NetLocal), ()), freshState ((default : Net.NetLocal), ()), freshState ((default : Net.NetLocal), ()), (⟨((default : Net.NetGlobal), ()), ∅⟩ : GlobalState), rfl, 0, robustStart_same (σ := freshState ((default : Net.NetLocal), ())) (by simp [system]) (fresh_freshState _)
    (by exts_init) (by exts_init)⟩

end github_com.mit_pdos.etcd_grove.examples.net.echo
end Perennial

end
