/- Lean-first (no Rocq counterpart).

# `raft/antithesis`: its top-level statement's premises are satisfiable

`premise_sat%` (`Robustness/PremiseSat.lean`): `raft_antithesis_robust`
(`Spec/github_com/mit_pdos/etcd_grove/examples/raft/antithesis/TopLevelRobustness.lean`) has no
premise beyond its instance binders (the package assumptions, `log.NewModel`), so it holds with
`Robust`'s antecedents: one fresh machine, its extension `idIssueExt` in its initial state. Checked
by `etc/premise-witness.py`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.TopLevelRobustness
public import Robustness.PremiseSat

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode
attribute [local instance] trivialExts trivialExtsSemantics trivialExtsInterp trivialExts_hasExt

open Robustness

theorem raft_antithesis_robust.premisesSat : premise_sat% raft_antithesis_robust.spec := by
  intros
  exact ⟨freshState ((∅ : IdIssueState), ()), ⟨((), ()), ∅⟩,
    (robustStart_one (fresh_freshState _) (by exts_init) (by exts_init)).1⟩

end EtcdGrove
end Perennial

end
