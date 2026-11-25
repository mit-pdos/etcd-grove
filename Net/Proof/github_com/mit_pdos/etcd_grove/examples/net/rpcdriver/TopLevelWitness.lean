/- Lean-first (no Rocq counterpart).

# Its top-level statement's premises are satisfiable

`premise_sat%` (`Robustness/PremiseSat.lean`): the statement of
`Net/Spec/github_com/mit_pdos/etcd_grove/examples/net/rpcdriver/TopLevelRobustness.lean` has premises that
hold together with `Robust`'s antecedents: two fresh machines (the server and the client) with no
listener, no connection, and `DistDeploy`'s addresses (`rpcAddrs`, distinct and valid, by evaluation).
Checked by `etc/premise-witness.py`.
-/
module

public import Net.Spec.github_com.mit_pdos.etcd_grove.examples.net.rpcdriver.TopLevelRobustness
public import Robustness.PremiseSat

@[expose] public section

noncomputable section

namespace Perennial
namespace github_com.mit_pdos.etcd_grove.examples.net.rpcdriver

open Iris Iris.BI Net
attribute [local instance] netExts netExtsSemantics netExtsInterp netExts_hasNet

open Robustness

theorem rpcdriver_robust.premisesSat : premise_sat% rpcdriver_robust.spec := by
  intros
  have hs : ∀ m, m ∈ [] ++ system (freshState ((default : Net.NetLocal), ())) (freshState ((default : Net.NetLocal), ())) → m.2 = freshState ((default : Net.NetLocal), ()) := by simp [system]
  refine ⟨freshState ((default : Net.NetLocal), ()), freshState ((default : Net.NetLocal), ()), (⟨((default : Net.NetGlobal), ()), ∅⟩ : GlobalState),
    ⟨by unfold rpcAddrs; decide, by unfold rpcAddrs; decide, rfl, fun m hm => by rw [hs m (by simpa using hm)]; rfl⟩,
    robustStart_same hs (fresh_freshState _) (by exts_init) (by exts_init)⟩

end github_com.mit_pdos.etcd_grove.examples.net.rpcdriver
end Perennial

end
