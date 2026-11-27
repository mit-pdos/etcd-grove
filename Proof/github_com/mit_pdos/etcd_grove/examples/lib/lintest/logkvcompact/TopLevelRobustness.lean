/- Lean-first (no Rocq counterpart).

# `lib/lintest/logkvcompact`: the top-level robustness result, proved

`logkvcompact_robust`, stated in
`Spec/github_com/mit_pdos/etcd_grove/examples/lib/lintest/logkvcompact/TopLevelRobustness.lean`,
from the example's closed theorem (`Adequacy.lean`).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.lib.lintest.logkvcompact.TopLevelRobustness
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.lintest.logkvcompact.Adequacy

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial

namespace EtcdGrove

namespace lintest

namespace logkvcompact

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

attribute [local instance] Robustness.noExts Robustness.noExtsSemantics Robustness.noExtsInterp

section adequacy

variable [go_gctx : GoGlobalContext]

/-- `logkvcompact_robust.spec`
(`Spec/github_com/mit_pdos/etcd_grove/examples/lib/lintest/logkvcompact/TopLevelRobustness.lean`). -/
theorem logkvcompact_robust : logkvcompact_robust.spec := by
  intro lctx sem package_sem σ g
  exact
    Robustness.Robust.of_single fun hf n κs t2 σ2 hn Hsteps =>
      (logkvcompact_adequate
        σ g hf.1 hf.2.1 hf.2.2 n hn κs t2 σ2 Hsteps).2

end adequacy
end logkvcompact
end lintest
end EtcdGrove
end Perennial

end
