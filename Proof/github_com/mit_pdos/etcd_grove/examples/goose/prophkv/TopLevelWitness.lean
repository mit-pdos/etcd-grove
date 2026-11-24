/- Lean-first (no Rocq counterpart).

# `goose/prophkv`: its top-level statements' premises are satisfiable

`premise_sat%` (`Robustness/PremiseSat.lean`): each statement of `Spec/github_com/mit_pdos/etcd_grove/examples/goose/prophkv/TopLevelRobustness.lean` has premises that hold
together with `Robust`'s antecedents (one fresh machine, its extension `idIssueExt` in any state).
Checked by `etc/premise-witness.py`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.goose.prophkv.TopLevelRobustness
public import Robustness.PremiseSat

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace goose_prophkv

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.goose.prophkv
attribute [local instance] trivialExts trivialExtsSemantics trivialExtsInterp

open Robustness

theorem goose_prophkv_robust.premisesSat : premise_sat% goose_prophkv_robust.spec := by
  intros
  exact ⟨freshState ((∅ : IdIssueState), ()), ⟨((), ()), ∅⟩, 0,
    (robustStart_one (fresh_freshState _) (by exts_init) (by exts_init)).1⟩

end goose_prophkv
end EtcdGrove
end Perennial

end
