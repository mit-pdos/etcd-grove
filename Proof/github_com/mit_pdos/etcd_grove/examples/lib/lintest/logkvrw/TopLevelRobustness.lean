/- Lean-first (no Rocq counterpart).

# `lib/lintest/logkvrw`: the top-level robustness result, proved

`logkvrw_robust`, stated in
`Spec/github_com/mit_pdos/etcd_grove/examples/lib/lintest/logkvrw/TopLevelRobustness.lean`,
from the example's closed theorem along the execution's thread bound (`logkvrw_adequate_below`,
`Adequacy.lean`).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.lib.lintest.logkvrw.TopLevelRobustness
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.lintest.logkvrw.Adequacy

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial

namespace EtcdGrove

namespace lintest

namespace logkvrw

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

attribute [local instance] trivialExts trivialExtsSemantics trivialExtsInterp trivialExts_hasExt

section adequacy

variable [go_gctx : GoGlobalContext]

/-- `logkvrw_robust.spec`
(`Spec/github_com/mit_pdos/etcd_grove/examples/lib/lintest/logkvrw/TopLevelRobustness.lean`). -/
theorem logkvrw_robust : logkvrw_robust.spec := by
  intro lctx sem package_sem σ g
  exact
    Robustness.Robust.of_single_below fun hf n κs t2 σ2 hn Hsteps =>
      (logkvrw_adequate_below
        σ g hf.1 hf.2.1 hf.2.2 (2 ^ 30) (Nat.le_refl _) n hn κs t2 σ2 Hsteps).2

end adequacy
end logkvrw
end lintest
end EtcdGrove
end Perennial

end
