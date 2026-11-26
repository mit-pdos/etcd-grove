/- Lean-first (no Rocq counterpart).

# Its top-level statement's premises are satisfiable

`premise_sat%` (`Robustness/PremiseSat.lean`): the statement of
`Net/Spec/github_com/mit_pdos/etcd_grove/examples/net/httpdriver/TopLevelRobustness.lean` has premises that
hold together with `Robust`'s antecedents: two fresh machines (the server and the client) with no
listener, no connection, and `DistDeploy`'s address (`httpAddrs`, valid, by evaluation). The
environment premise `HEnv` (`GodebugHttpmuxgo121Not1`, over the opaque `godebugHttpmuxgo121`) is
left out (`etc/premise-witness-baseline.txt`).
Checked by `etc/premise-witness.py`.
-/
module

public import Net.Spec.github_com.mit_pdos.etcd_grove.examples.net.httpdriver.TopLevelRobustness
public import Robustness.PremiseSat

@[expose] public section

noncomputable section

namespace Perennial
namespace github_com.mit_pdos.etcd_grove.examples.net.httpdriver

open Iris Iris.BI Net
attribute [local instance] netExts netExtsSemantics netExtsInterp netExts_hasNet

open Robustness

theorem httpdriver_robust.premisesSat : premise_sat% httpdriver_robust.spec without [HEnv] := by
  intros
  have hs : ∀ m, m ∈ [] ++ system (freshState ((default : Net.NetLocal), ())) (freshState ((default : Net.NetLocal), ())) → m.2 = freshState ((default : Net.NetLocal), ()) := by simp [system]
  refine ⟨freshState ((default : Net.NetLocal), ()), freshState ((default : Net.NetLocal), ()), (⟨((default : Net.NetGlobal), ()), ∅⟩ : GlobalState),
    ⟨by unfold httpAddrs; decide, by unfold httpAddrs; decide, rfl, fun m hm => by rw [hs m (by simpa using hm)]; rfl⟩,
    robustStart_same hs (fresh_freshState _) (by exts_init) (by exts_init)⟩

end github_com.mit_pdos.etcd_grove.examples.net.httpdriver
end Perennial

end
