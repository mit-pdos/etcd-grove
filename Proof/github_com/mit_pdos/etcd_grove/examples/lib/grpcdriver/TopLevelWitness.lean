/- Lean-first (no Rocq counterpart).

# `lib/grpcdriver`: its top-level statement's premises can hold

`grpcdriver_robust.premisesSat` (`Robustness/PremiseSat.lean`): two fresh machines with the net
extension's initial local state, the empty global state, and the deployment's address valid and
distinct (by `decide`), as net/rpc's driver's witness.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver.TopLevelRobustness
public import Robustness.PremiseSat

@[expose] public section

noncomputable section

namespace Perennial
namespace github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver

open Iris Iris.BI Net
attribute [local instance] netExts netExtsSemantics netExtsInterp netExts_hasNet

open Robustness

theorem grpcdriver_robust.premisesSat : premise_sat% grpcdriver_robust.spec := by
  intros
  have hs : ∀ m, m ∈ [] ++ system (freshState ((default : Net.NetLocal), ()))
      (freshState ((default : Net.NetLocal), ())) → m.2 = freshState ((default : Net.NetLocal), ()) := by
    simp [system]
  refine ⟨freshState ((default : Net.NetLocal), ()), freshState ((default : Net.NetLocal), ()),
    (⟨((default : Net.NetGlobal), ()), ∅⟩ : GlobalState),
    ⟨by unfold grpcAddrs; decide, by unfold grpcAddrs; decide, rfl,
      fun m hm => by rw [hs m (by simpa using hm)]; rfl⟩,
    robustStart_same hs (fresh_freshState _) (by exts_init) (by exts_init)⟩

end github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver
end Perennial

end
