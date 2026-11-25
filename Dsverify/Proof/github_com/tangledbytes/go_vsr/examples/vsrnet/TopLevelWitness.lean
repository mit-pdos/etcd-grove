/- Lean-first (no Rocq counterpart).

# Its top-level statement's premises are satisfiable

`premise_sat%` (`Robustness/PremiseSat.lean`): the statement of
`Dsverify/Spec/github_com/tangledbytes/go_vsr/examples/vsrnet/TopLevelRobustness.lean` has premises
that hold together with `Robust`'s antecedents: twelve fresh machines with no listener, no
connection, and `DistDeploy`'s addresses (`vrKitAddrs`, distinct and valid, by evaluation). The JSON
premise (`∃ DecoderRep, JsonHyps`, an Iris contract at each machine's heap) is left out by
`premise_sat%` itself; its instance is `NonVacuityLinked.lean`'s (over local axioms, test-only).
Checked by `etc/premise-witness.py`.
-/
module

public import Dsverify.Spec.github_com.tangledbytes.go_vsr.examples.vsrnet.TopLevelRobustness
public import Robustness.PremiseSat

@[expose] public section

noncomputable section

set_option maxRecDepth 100000

namespace Perennial
namespace github_com.tangledbytes.go_vsr.examples.vsrnet

open Iris Iris.BI Net
attribute [local instance] netExts netExtsSemantics netExtsInterp netExts_hasNet

open Robustness

theorem vr_remote_robust.premisesSat : premise_sat% vr_remote_robust.spec := by
  intros
  have hs : ∀ m, m ∈ [] ++ system (fun _ => freshState ((default : Net.NetLocal), ())) →
      m.2 = freshState ((default : Net.NetLocal), ()) := by simp [system]
  refine ⟨fun _ => freshState ((default : Net.NetLocal), ()),
    (⟨((default : Net.NetGlobal), ()), ∅⟩ : GlobalState), 0,
    ⟨by unfold vrKitAddrs VsrWire.addrs cfgAddrs clientAddrs; decide,
     by unfold vrKitAddrs VsrWire.addrs cfgAddrs clientAddrs; decide, rfl,
     fun m hm => by rw [hs m (by simpa using hm)]; rfl⟩,
    robustStart_same hs (fresh_freshState _) (by exts_init) (by exts_init)⟩

end github_com.tangledbytes.go_vsr.examples.vsrnet
end Perennial

end
