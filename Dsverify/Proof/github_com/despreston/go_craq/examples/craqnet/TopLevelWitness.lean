/- Lean-first (no Rocq counterpart).

# Its top-level statement's premises are satisfiable

`premise_sat%` (`Robustness/PremiseSat.lean`): the statement of
`Dsverify/Spec/github_com/despreston/go_craq/examples/craqnet/TopLevelRobustness.lean` has premises
that hold together with `Robust`'s antecedents: thirteen fresh machines with no listener, no
connection, and `DistDeploy`'s addresses (`craqKitAddrs`, distinct and valid, by evaluation); its premises `LogHyp` and `RpcHttpServe` are Iris contracts, left out by `premise_sat%` itself.
Checked by `etc/premise-witness.py`.
-/
module

public import Dsverify.Spec.github_com.despreston.go_craq.examples.craqnet.TopLevelRobustness
public import Robustness.PremiseSat

@[expose] public section

noncomputable section

set_option maxRecDepth 100000

namespace Perennial
namespace github_com.despreston.go_craq.examples.craqnet

open Iris Iris.BI Net
attribute [local instance] netExts netExtsSemantics netExtsInterp netExts_hasNet

open Robustness

theorem craq_remote_robust.premisesSat : premise_sat% craq_remote_robust.spec := by
  intros
  have hs : ∀ m, m ∈ [] ++ system (fun _ => freshState ((default : Net.NetLocal), ())) →
      m.2 = freshState ((default : Net.NetLocal), ()) := by simp [system]
  refine ⟨fun _ => freshState ((default : Net.NetLocal), ()),
    (⟨((default : Net.NetGlobal), ()), ∅⟩ : GlobalState),
    ⟨by unfold craqKitAddrs; decide +kernel, by unfold craqKitAddrs; decide +kernel, rfl,
     fun m hm => by rw [hs m (by simpa using hm)]; rfl⟩,
    robustStart_same hs (fresh_freshState _) (by exts_init) (by exts_init)⟩

end github_com.despreston.go_craq.examples.craqnet
end Perennial

end
