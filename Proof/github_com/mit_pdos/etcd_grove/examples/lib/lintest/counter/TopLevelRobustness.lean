/- Lean-first (no Rocq counterpart).

# `lib/lintest/counter`: the top-level robustness result, proved

`counter_robust`, stated in
`Spec/github_com/mit_pdos/etcd_grove/examples/lib/lintest/counter/TopLevelRobustness.lean`,
from the example's closed theorem (`Adequacy.lean`).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.lib.lintest.counter.TopLevelRobustness
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.lintest.counter.Adequacy

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial

namespace EtcdGrove

namespace lintest

namespace counter

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

attribute [local instance] Robustness.noExts Robustness.noExtsSemantics Robustness.noExtsInterp

section adequacy

variable [go_gctx : GoGlobalContext]

/-- `counter_robust.spec`
(`Spec/github_com/mit_pdos/etcd_grove/examples/lib/lintest/counter/TopLevelRobustness.lean`). -/
theorem counter_robust : counter_robust.spec := by
  intro lctx sem package_sem σ g
  exact
    Robustness.Robust.of_single fun hf n κs t2 σ2 hn Hsteps =>
      (counter_adequate
        σ g hf.1 hf.2.1 hf.2.2 n hn κs t2 σ2 Hsteps).2

end adequacy
end counter
end lintest
end EtcdGrove
end Perennial

end
