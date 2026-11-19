/- Lean-first (no Rocq counterpart).

# `k8s/smd`: the top-level robustness result, proved

`smd_driver_robust`, stated in `Spec/github_com/mit_pdos/etcd_grove/examples/k8s/smd/TopLevelRobustness.lean`, from the driver's closed theorem
(`Results.lean`).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.smd.TopLevelRobustness
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.smd.Results

@[expose] public section

noncomputable section

set_option linter.iris.style.nameCheck false

namespace Perennial

namespace EtcdGrove

namespace k8s_smd

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

attribute [local instance] trivialExts trivialExtsSemantics trivialExtsInterp

section program

variable [go_gctx : GoGlobalContext]

/-- `smd_driver_robust.spec` (`Spec/github_com/mit_pdos/etcd_grove/examples/k8s/smd/TopLevelRobustness.lean`). -/
theorem smd_driver_robust : smd_driver_robust.spec := by
  intro lctx sem package_sem σ g bound
  exact
    Robustness.Robust.of_single fun hf n κs t2 σ2 _ Hsteps =>
      (smd_driver_safe σ g hf.1 hf.2.1 hf.2.2 n κs t2 σ2 Hsteps).2

end program
end k8s_smd
end EtcdGrove
end Perennial

end
