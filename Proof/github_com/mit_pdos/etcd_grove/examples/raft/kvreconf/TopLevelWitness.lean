/- Lean-first (no Rocq counterpart).

# `raft/kvreconf`: its top-level statements' premises are satisfiable

`premise_sat%` (`Robustness/PremiseSat.lean`): each statement of `Spec/github_com/mit_pdos/etcd_grove/examples/raft/kvreconf/TopLevelRobustness.lean` has premises that hold
together with `Robust`'s antecedents (one fresh machine, its extension `idIssueExt` in any state).
Checked by `etc/premise-witness.py`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvreconf.TopLevelRobustness
public import Robustness.PremiseSat

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3
attribute [local instance] trivialExts trivialExtsSemantics trivialExtsInterp trivialExts_hasExt

open Robustness

theorem raft_kvreconf_porcupine_robust.premisesSat : premise_sat% raft_kvreconf_porcupine_robust.spec := by
  intros
  exact ⟨freshState ((∅ : IdIssueState), ()), ⟨((), ()), ∅⟩,
    (robustStart_one (fresh_freshState _) (by exts_init) (by exts_init)).1⟩

theorem raft_kvreconfN_porcupine_robust.premisesSat : premise_sat% raft_kvreconfN_porcupine_robust.spec := by
  intros
  exact ⟨1, freshState ((∅ : IdIssueState), ()), ⟨((), ()), ∅⟩,
    (robustStart_one (fresh_freshState _) (by exts_init) (by exts_init)).1⟩

end EtcdGrove
end Perennial

end
