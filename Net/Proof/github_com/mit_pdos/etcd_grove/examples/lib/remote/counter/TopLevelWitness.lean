/- Lean-first (no Rocq counterpart).

# Its top-level statement's premises are satisfiable

`premise_sat%` (`Robustness/PremiseSat.lean`): the statement of `Net/Spec/github_com/mit_pdos/etcd_grove/examples/lib/remote/counter/TopLevelRobustness.lean` has premises that hold
together with `Robust`'s antecedents: four fresh machines with no listener, no connection, and `DistDeploy`'s addresses (`counterAddrs`, distinct and valid, by evaluation). Checked by `etc/premise-witness.py`.
-/
module

public import Net.Spec.github_com.mit_pdos.etcd_grove.examples.lib.remote.counter.TopLevelRobustness
public import Robustness.PremiseSat

@[expose] public section

noncomputable section

namespace Perennial
namespace github_com.mit_pdos.etcd_grove.examples.lib.remote.counter



open Iris Iris.BI Net
attribute [local instance] netExts netExtsSemantics netExtsInterp netExts_hasNet

open Robustness

theorem counter_remote_robust.premisesSat : premise_sat% counter_remote_robust.spec := by
  intros
  have hs : ∀ m, m ∈ [] ++ system (freshState ((default : Net.NetLocal), ())) (freshState ((default : Net.NetLocal), ())) (freshState ((default : Net.NetLocal), ())) (freshState ((default : Net.NetLocal), ())) → m.2 = freshState ((default : Net.NetLocal), ()) := by simp [system]
  refine ⟨freshState ((default : Net.NetLocal), ()), freshState ((default : Net.NetLocal), ()), freshState ((default : Net.NetLocal), ()), freshState ((default : Net.NetLocal), ()), (⟨((default : Net.NetGlobal), ()), ∅⟩ : GlobalState), 0,
    ⟨by unfold counterAddrs; decide, by unfold counterAddrs; decide, rfl, fun m hm => by rw [hs m (by simpa using hm)]; rfl⟩,
    robustStart_same hs (fresh_freshState _) (by exts_init) (by exts_init)⟩

end github_com.mit_pdos.etcd_grove.examples.lib.remote.counter
end Perennial

end
