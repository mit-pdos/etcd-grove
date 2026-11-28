/- Lean-first (no Rocq counterpart).

# Its top-level statement's premises are satisfiable

`premise_sat%` (`Robustness/PremiseSat.lean`): the statement of
`Dsverify/Spec/github_com/hashicorp/raft/examples/hraftnet/TopLevelRobustness.lean` has premises
that hold together with `Robust`'s antecedents: twelve fresh machines with no listener, no
connection, and `DistDeploy`'s addresses (`hraftKitAddrs`, distinct and valid, by evaluation): the statement has no other premise.
`hraft_robust`: twelve fresh machines with no listener, each with a file system whose only root is
`/var/lib/hraft`, an empty directory (`Robustness/FsStart.lean`), and a network with no connection.
Checked by `etc/premise-witness.py`.
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.TopLevelRobustness
public import Robustness.PremiseSat
public import Robustness.FsStart

@[expose] public section

noncomputable section

set_option maxRecDepth 100000

namespace Perennial
namespace github_com.hashicorp.raft.examples.hraftnet

open Iris Iris.BI Net
section nocrash
attribute [local instance] netExts netExtsSemantics netExtsInterp netExts_hasNet

open Robustness

theorem hraft_nocrash_robust.premisesSat : premise_sat% hraft_nocrash_robust.spec := by
  intros
  have hs : ∀ m, m ∈ [] ++ system (fun _ => freshState ((default : Net.NetLocal), ())) →
      m.2 = freshState ((default : Net.NetLocal), ()) := by simp [system]
  refine ⟨fun _ => freshState ((default : Net.NetLocal), ()),
    (⟨((default : Net.NetGlobal), ()), ∅⟩ : GlobalState),
    ⟨by unfold hraftKitAddrs; decide +kernel, by unfold hraftKitAddrs; decide +kernel, rfl,
     fun m hm => by rw [hs m (by simpa using hm)]; rfl⟩,
    robustStart_same hs (fresh_freshState _) (by exts_init) (by exts_init)⟩

end nocrash

section crash
open NetFs Fs Robustness
attribute [local instance] kvraftExts kvraftExtsSemantics kvraftExts_hasNet kvraftExts_hasFs

/-- The servers' data directory, a root's form. -/
theorem hraftDataDir_rootForm : RootForm hraftDataDir :=
  ⟨[go!"var", go!"lib", go!"hraft"], by simp, by decide, by decide⟩

theorem hraft_robust.premisesSat : premise_sat% hraft_robust.spec := by
  intros
  have hs : ∀ m, m ∈ crashServers (fun _ => freshState ((default : Net.NetLocal), (fsOneRoot hraftDataDir, ())))
      ++ stableMachines (fun _ => freshState ((default : Net.NetLocal), (fsOneRoot hraftDataDir, ()))) →
      m.2 = freshState ((default : Net.NetLocal), (fsOneRoot hraftDataDir, ())) := by
    simp [crashServers, stableMachines]
  refine ⟨fun _ => freshState ((default : Net.NetLocal), (fsOneRoot hraftDataDir, ())),
    (⟨((default : Net.NetGlobal), ((), ())), ∅⟩ : GlobalState),
    fun _ _ _ => ⟨fsOneRoot_root_mem _, fun c => fsOneRoot_lookup_joinPath _ _ (List.cons_ne_nil _ _)⟩,
    robustStart_same hs (fresh_freshState _) (by exts_init) ⟨rfl, fsInit_fsOneRoot _ hraftDataDir_rootForm, trivial⟩⟩

end crash

end github_com.hashicorp.raft.examples.hraftnet
end Perennial

end
