/- Lean-first (no Rocq counterpart).

# `raft/kvwitness`: its top-level statements' premises are satisfiable

`premise_sat%` (`Robustness/PremiseSat.lean`): each statement of `RaftWitness/Spec/github_com/mit_pdos/etcd_grove/examples/raft/kvwitness/TopLevelRobustness.lean` has premises that hold
together with `Robust`'s antecedents (one fresh machine, its extension `idIssueExt` in any state).
Checked by `etc/premise-witness.py`.
-/
module

public import RaftWitness.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvwitness.TopLevelRobustness
public import Robustness.PremiseSat

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3
attribute [local instance] trivialExts trivialExtsSemantics trivialExtsInterp

open Robustness

theorem kv_porcupine_robust.premisesSat : premise_sat% kv_porcupine_robust.spec := by
  intros
  exact ⟨freshState ((∅ : IdIssueState), ()), ⟨((), ()), ∅⟩,
    (robustStart_one (fresh_freshState _) (by exts_init) (by exts_init)).1⟩

theorem raft_kvwitness_porcupine_robust.premisesSat : premise_sat% raft_kvwitness_porcupine_robust.spec := by
  intros
  exact ⟨freshState ((∅ : IdIssueState), ()), ⟨((), ()), ∅⟩,
    (robustStart_one (fresh_freshState _) (by exts_init) (by exts_init)).1⟩

end EtcdGrove
end Perennial

end
