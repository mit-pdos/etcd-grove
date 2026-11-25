/- Lean-first (no Rocq counterpart).

# Its top-level statement's premises are satisfiable

`premise_sat%` (`Robustness/PremiseSat.lean`): the statement of
`Dsverify/Spec/gryff/examples/gryffnet/TopLevelRobustness.lean` has premises
that hold together with `Robust`'s antecedents: eleven fresh machines with no listener, no
connection, and `DistDeploy`'s addresses (`gryffKitAddrs`, distinct and valid, by evaluation): the
statement has no other premise. Checked by `etc/premise-witness.py`.
-/
module

public import Dsverify.Spec.gryff.examples.gryffnet.TopLevelRobustness
public import Robustness.PremiseSat

@[expose] public section

noncomputable section

set_option maxRecDepth 100000

namespace Perennial
namespace gryff.examples.gryffnet

open Iris Iris.BI Net
attribute [local instance] netExts netExtsSemantics netExtsInterp netExts_hasNet

open Robustness

theorem gryff_remote_robust.premisesSat : premise_sat% gryff_remote_robust.spec := by
  intros
  have hs : ∀ m, m ∈ [] ++ system (fun _ => freshState ((default : Net.NetLocal), ())) →
      m.2 = freshState ((default : Net.NetLocal), ()) := by simp [system]
  refine ⟨fun _ => freshState ((default : Net.NetLocal), ()),
    (⟨((default : Net.NetGlobal), ()), ∅⟩ : GlobalState),
    ⟨by unfold gryffKitAddrs; decide, by unfold gryffKitAddrs; decide, rfl,
     fun m hm => by rw [hs m (by simpa using hm)]; rfl⟩,
    robustStart_same hs (fresh_freshState _) (by exts_init) (by exts_init)⟩

end gryff.examples.gryffnet
end Perennial

end
