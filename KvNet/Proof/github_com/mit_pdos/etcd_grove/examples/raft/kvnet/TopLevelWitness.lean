/- Lean-first (no Rocq counterpart).

# `raft/kvnet`: its top-level statements' premises are satisfiable

`premise_sat%` (`Robustness/PremiseSat.lean`): the premises of `raft_kvnet_robust` (lean's statement)
and of `raft_kvnet_robust_example` hold together with `Robust`'s antecedents. Every machine is fresh,
with no listener (the net extension's initial state) and a file system whose only root is
`/var/lib/kvnet`, an empty directory (`Robustness/FsStart.lean`), so nothing is below it
(`fsOneRoot_lookup_joinPath`); the network has no connection. For `raft_kvnet_robust`: one replica at
`10.0.0.1:7001`, the example's options with one bootstrap voter (`ClusterConfig.Ok 1`, by evaluation).
Checked by `etc/premise-witness.py`.
-/
module

public import KvNet.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.TopLevelRobustness
public import Robustness.FsStart

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial
namespace EtcdGrove
namespace raft_kvnet

open NetFs
attribute [local instance] kvnetExts kvnetExtsSemantics kvnetExts_hasNet kvnetExts_hasFs

open Robustness Fs

/-- The replicas' directory, a root's form. -/
theorem kvnetDir_rootForm : RootForm go!"/var/lib/kvnet" :=
  ⟨[go!"var", go!"lib", go!"kvnet"], by simp, by decide, by decide⟩

/-- The example's options with one bootstrap voter. -/
def oneVoterConfig : ClusterConfig := { exampleConfig with voters := 1 }

theorem raft_kvnet_robust.premisesSat : premise_sat% raft_kvnet_robust.spec := by
  intros
  refine ⟨oneVoterConfig, go!"/var/lib/kvnet",
    [(go!"10.0.0.1:7001", freshState ((default : Net.NetLocal), (fsOneRoot go!"/var/lib/kvnet", ())))],
    freshState ((default : Net.NetLocal), (fsOneRoot go!"/var/lib/kvnet", ())),
    (⟨((default : Net.NetGlobal), ((), ())), ∅⟩ : GlobalState),
    by show oneVoterConfig.Ok 1; unfold ClusterConfig.Ok oneVoterConfig exampleConfig; decide,
    by simp, by decide, by simp,
    ?_, robustStart_same (σ := freshState ((default : Net.NetLocal), (fsOneRoot go!"/var/lib/kvnet", ())))
      ?_ (fresh_freshState _) (by exts_init) ?_⟩
  · intro a σ h
    simp only [List.mem_singleton, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨by decide, fsOneRoot_root_mem _,
      fun c => fsOneRoot_lookup_joinPath _ _ (List.cons_ne_nil _ _)⟩
  · intro m hm
    simp at hm
    rcases hm with h | h <;> subst h <;> rfl
  · exact ⟨rfl, fsInit_fsOneRoot _ kvnetDir_rootForm, trivial⟩

theorem raft_kvnet_robust_example.premisesSat : premise_sat% raft_kvnet_robust_example.spec := by
  intros
  refine ⟨freshState ((default : Net.NetLocal), (fsOneRoot go!"/var/lib/kvnet", ())),
    freshState ((default : Net.NetLocal), (fsOneRoot go!"/var/lib/kvnet", ())),
    freshState ((default : Net.NetLocal), (fsOneRoot go!"/var/lib/kvnet", ())),
    freshState ((default : Net.NetLocal), (fsOneRoot go!"/var/lib/kvnet", ())),
    freshState ((default : Net.NetLocal), (fsOneRoot go!"/var/lib/kvnet", ())),
    freshState ((default : Net.NetLocal), (fsOneRoot go!"/var/lib/kvnet", ())),
    (⟨((default : Net.NetGlobal), ((), ())), ∅⟩ : GlobalState),
    ?_, robustStart_same (σ := freshState ((default : Net.NetLocal), (fsOneRoot go!"/var/lib/kvnet", ())))
      ?_ (fresh_freshState _) (by exts_init) ?_⟩
  · intro σ hσ
    have h : σ = freshState ((default : Net.NetLocal), (fsOneRoot go!"/var/lib/kvnet", ())) := by
      simpa using hσ
    subst h
    exact ⟨fsOneRoot_root_mem _, fun c => fsOneRoot_lookup_joinPath _ _ (List.cons_ne_nil _ _)⟩
  · intro m hm
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with (h | h | h | h | h) | h <;> subst h <;> rfl
  · exact ⟨rfl, fsInit_fsOneRoot _ kvnetDir_rootForm, trivial⟩

end raft_kvnet
end EtcdGrove
end Perennial

end
