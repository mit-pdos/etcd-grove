/- Lean-first (no Rocq counterpart).

# `raft/kvraft`: its top-level statements' premises are satisfiable

`premise_sat%` (`Robustness/PremiseSat.lean`): the premises of `kvraft_robust` (lean's statement)
and of `kvraft_robust_example` hold together with `Robust`'s antecedents. Every machine is fresh,
with no listener (the net extension's initial state) and a file system whose only root is
`/var/lib/kvraft`, an empty directory (`Robustness/FsStart.lean`), so nothing is below it
(`fsOneRoot_lookup_joinPath`); the network has no connection. For `kvraft_robust`: one replica at
`10.0.0.1:7001`, the example's options with one bootstrap voter (the cluster's options and addresses
are checked in Go since P8, so the statement has no premise on them).
Checked by `etc/premise-witness.py`.
-/
module

public import KvRaft.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.TopLevelRobustness
public import Robustness.FsStart

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial
namespace EtcdGrove
namespace kvraft

open NetFs
attribute [local instance] kvraftExts kvraftExtsSemantics kvraftExts_hasNet kvraftExts_hasFs

open Robustness Fs

/-- The replicas' directory, a root's form. -/
theorem kvraftDir_rootForm : RootForm go!"/var/lib/kvraft" :=
  ⟨[go!"var", go!"lib", go!"kvraft"], by simp, by decide, by decide⟩

/-- The example's options with one bootstrap voter. -/
def oneVoterConfig : ClusterConfig := { exampleConfig with voters := 1 }

theorem kvraft_robust.premisesSat : premise_sat% kvraft_robust.spec := by
  intros
  refine ⟨oneVoterConfig, go!"/var/lib/kvraft",
    [(go!"10.0.0.1:7001", freshState ((default : Net.NetLocal), (fsOneRoot go!"/var/lib/kvraft", ())))],
    freshState ((default : Net.NetLocal), (fsOneRoot go!"/var/lib/kvraft", ())),
    (⟨((default : Net.NetGlobal), ((), ())), ∅⟩ : GlobalState),
    ?_, robustStart_same (σ := freshState ((default : Net.NetLocal), (fsOneRoot go!"/var/lib/kvraft", ())))
      ?_ (fresh_freshState _) (by exts_init) ?_⟩
  · intro a σ h
    simp only [List.mem_singleton, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨fsOneRoot_root_mem _, fun c => fsOneRoot_lookup_joinPath _ _ (List.cons_ne_nil _ _)⟩
  · intro m hm
    simp at hm
    rcases hm with h | h <;> subst h <;> rfl
  · exact ⟨rfl, fsInit_fsOneRoot _ kvraftDir_rootForm, trivial⟩

theorem kvraft_robust_example.premisesSat : premise_sat% kvraft_robust_example.spec := by
  intros
  refine ⟨freshState ((default : Net.NetLocal), (fsOneRoot go!"/var/lib/kvraft", ())),
    freshState ((default : Net.NetLocal), (fsOneRoot go!"/var/lib/kvraft", ())),
    freshState ((default : Net.NetLocal), (fsOneRoot go!"/var/lib/kvraft", ())),
    freshState ((default : Net.NetLocal), (fsOneRoot go!"/var/lib/kvraft", ())),
    freshState ((default : Net.NetLocal), (fsOneRoot go!"/var/lib/kvraft", ())),
    freshState ((default : Net.NetLocal), (fsOneRoot go!"/var/lib/kvraft", ())),
    (⟨((default : Net.NetGlobal), ((), ())), ∅⟩ : GlobalState),
    ?_, robustStart_same (σ := freshState ((default : Net.NetLocal), (fsOneRoot go!"/var/lib/kvraft", ())))
      ?_ (fresh_freshState _) (by exts_init) ?_⟩
  · intro σ hσ
    have h : σ = freshState ((default : Net.NetLocal), (fsOneRoot go!"/var/lib/kvraft", ())) := by
      simpa using hσ
    subst h
    exact ⟨fsOneRoot_root_mem _, fun c => fsOneRoot_lookup_joinPath _ _ (List.cons_ne_nil _ _)⟩
  · intro m hm
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with (h | h | h | h | h) | h <;> subst h <;> rfl
  · exact ⟨rfl, fsInit_fsOneRoot _ kvraftDir_rootForm, trivial⟩

end kvraft
end EtcdGrove
end Perennial

end
