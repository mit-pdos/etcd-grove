/- Lean-first (no Rocq counterpart).

# `k8s/authz`: its top-level statements' premises are satisfiable

`premise_sat%` (`Robustness/PremiseSat.lean`): each statement of `Spec/github_com/mit_pdos/etcd_grove/examples/k8s/authz/TopLevelRobustness.lean` has premises that hold
together with `Robust`'s antecedents (one fresh machine, its extension `idIssueExt` in any state).
Checked by `etc/premise-witness.py`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.authz.TopLevelRobustness
public import Robustness.PremiseSat

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_authz

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
attribute [local instance] idIssueExts idIssueExtsSemantics idIssueExtsInterp idIssueExts_hasExt

open Robustness

theorem k8s_authz_robust.premisesSat : premise_sat% k8s_authz_robust.spec := by
  intros
  exact ⟨freshState ((∅ : IdIssueState), ()), ⟨((), ()), ∅⟩, 0,
    (robustStart_one (fresh_freshState _) (by exts_init) (by exts_init)).1⟩

end k8s_authz
end EtcdGrove
end Perennial

end
