/- Lean-first (no Rocq counterpart).

# `mvccrand`: the top-level robustness result, proved

`mvccrand_robust`, stated in
`Spec/github_com/mit_pdos/etcd_grove/examples/mvccrand/TopLevelRobustness.lean`,
from the example's closed theorem (`Adequacy.lean`).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccrand.TopLevelRobustness

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

set_option synthInstance.maxSize 4096

set_option synthInstance.maxHeartbeats 400000

namespace Perennial

namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

attribute [local instance] trivialExts trivialExtsSemantics trivialExtsInterp trivialExts_hasExt

section adequacy

variable [go_gctx : GoGlobalContext]

/-- `mvccrand_robust.spec`
(`Spec/github_com/mit_pdos/etcd_grove/examples/mvccrand/TopLevelRobustness.lean`). -/
theorem mvccrand_robust : mvccrand_robust.spec := by
  intro lctx sem package_sem mvcc_sem srv_sem cache_sem Hsort Hdbo Hdbc HFs HEnv σ g
  exact
    Robustness.Robust.of_single fun hf n κs t2 σ2 hn Hsteps =>
      (mvccrand_adequate
        Hsort Hdbo Hdbc HFs HEnv σ g hf.1 hf.2.1 hf.2.2 n κs t2 σ2 Hsteps (by omega)).2

end adequacy
end EtcdGrove
end Perennial

end
