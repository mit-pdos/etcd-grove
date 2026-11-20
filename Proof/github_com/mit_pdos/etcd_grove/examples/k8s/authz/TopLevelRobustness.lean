/- Lean-first (no Rocq counterpart).

# `k8s/authz`: the top-level robustness result, proved

`k8s_authz_robust`, stated in
`Spec/github_com/mit_pdos/etcd_grove/examples/k8s/authz/TopLevelRobustness.lean`,
from the example's closed theorem (`Results.lean`).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.authz.TopLevelRobustness
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.authz.Results

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial

namespace EtcdGrove

namespace k8s_authz

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

attribute [local instance] trivialExts trivialExtsSemantics trivialExtsInterp trivialExts_hasExt

section program

variable [go_gctx : GoGlobalContext]

/-- `k8s_authz_robust.spec`
(`Spec/github_com/mit_pdos/etcd_grove/examples/k8s/authz/TopLevelRobustness.lean`). -/
theorem k8s_authz_robust : k8s_authz_robust.spec := by
  intro lctx sem package_sem σ g bound
  exact
    Robustness.Robust.of_single fun hf n κs t2 σ2 _ Hsteps =>
      (k8s_authz_safe σ g hf.1 hf.2.1 hf.2.2 n κs t2 σ2 Hsteps).2

end program
end k8s_authz
end EtcdGrove
end Perennial

#print axioms Perennial.EtcdGrove.k8s_authz.k8s_authz_robust

end
