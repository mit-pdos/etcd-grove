/- Lean-first (no Rocq counterpart).

# Its top-level statement's premises are satisfiable

`premise_sat%` (`Robustness/PremiseSat.lean`): the statement of
`Dsverify/Spec/github_com/imdea_software/swiftpaxos/examples/swiftnet/TopLevelRobustness.lean` has premises
that hold together with `Robust`'s antecedents: thirteen fresh machines with no listener, no
connection, and `DistDeploy`'s addresses (`swAddrs`, distinct and valid, by evaluation); the statement has no other premise.
Checked by `etc/premise-witness.py`.
-/
module

public import Dsverify.Spec.github_com.imdea_software.swiftpaxos.examples.swiftnet.TopLevelRobustness
public import Robustness.PremiseSat

@[expose] public section

noncomputable section

set_option maxRecDepth 100000

namespace Perennial
namespace github_com.imdea_software.swiftpaxos.examples.swiftnet

open Iris Iris.BI Net Dsv
attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp netShaExts_has

open Robustness

theorem swiftpaxos_remote_robust.premisesSat : premise_sat% swiftpaxos_remote_robust.spec := by
  intros
  have hs : ∀ m, m ∈ [] ++ system (fun _ => freshState (default : ExtsLocalState netShaExts.1)) →
      m.2 = freshState (default : ExtsLocalState netShaExts.1) := by simp [system]
  refine ⟨fun _ => freshState (default : ExtsLocalState netShaExts.1),
    (⟨(default : ExtsGlobalState netShaExts.1), ∅⟩ : GlobalState),
    ⟨by unfold swAddrs; decide +kernel, by unfold swAddrs; decide +kernel, rfl,
     fun m hm => by rw [hs m (by simpa using hm)]; rfl⟩,
    robustStart_same hs (fresh_freshState _) (by exts_init) (by exts_init)⟩

end github_com.imdea_software.swiftpaxos.examples.swiftnet
end Perennial

end
