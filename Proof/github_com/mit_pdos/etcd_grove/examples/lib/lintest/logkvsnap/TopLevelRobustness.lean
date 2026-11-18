/- Lean-first (no Rocq counterpart).

# `lib/lintest/logkvsnap`: the top-level robustness result, proved

`logkvsnap_robust`, stated in
`Spec/github_com/mit_pdos/etcd_grove/examples/lib/lintest/logkvsnap/TopLevelRobustness.lean`,
from the example's closed theorem (`Adequacy.lean`).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.lib.lintest.logkvsnap.TopLevelRobustness

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial

namespace EtcdGrove

namespace lintest

namespace logkvsnap

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

attribute [local instance] trivialExts trivialExtsSemantics trivialExtsInterp trivialExts_hasExt

section adequacy

variable [go_gctx : GoGlobalContext]

/-- `logkvsnap_robust.spec`
(`Spec/github_com/mit_pdos/etcd_grove/examples/lib/lintest/logkvsnap/TopLevelRobustness.lean`). -/
theorem logkvsnap_robust : logkvsnap_robust.spec := by
  intro lctx sem package_sem σ g
  exact
    Robustness.Robust.of_single fun hf n κs t2 σ2 hn Hsteps =>
      (logkvsnap_adequate
        σ g hf.1 hf.2.1 hf.2.2 n (by omega) κs t2 σ2 Hsteps).2

end adequacy
end logkvsnap
end lintest
end EtcdGrove
end Perennial

end
