/- Lean-first (no Rocq counterpart).

# `mvccrand`: the top-level robustness result, proved

`mvccrand_robust`, stated in
`Spec/github_com/mit_pdos/etcd_grove/examples/mvccrand/TopLevelRobustness.lean`,
from the example's closed theorem (`Adequacy.lean`).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccrand.TopLevelRobustness
public import Proof.github_com.mit_pdos.etcd_grove.examples.mvccrand.Adequacy

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

set_option synthInstance.maxSize 4096

set_option synthInstance.maxHeartbeats 400000

namespace Perennial

namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

attribute [local instance] etcdFsExts etcdFsExtsSemantics etcdFsExtsInterp etcdFsExts_hasIdIssue
  etcdFsExts_hasFs etcdFsSem etcdFsSemOk etcdFsNoErr

section adequacy

variable [go_gctx : GoGlobalContext]

/-- `mvccrand_robust.spec`
(`Spec/github_com/mit_pdos/etcd_grove/examples/mvccrand/TopLevelRobustness.lean`). -/
theorem mvccrand_robust : mvccrand_robust.spec := by
  intro lctx sem package_sem srv_sem cache_sem Hsort _ _ r HEnv σ g Hfs j0 Hr
  exact
    Robustness.Robust.of_single_below fun hf n κs t2 σ2 hn Hsteps =>
      (mvccrand_adequate_below
        Hsort r HEnv σ g hf.1 hf.2.1 Hfs j0 Hr hf.2.2 (2 ^ 28) (Nat.le_refl _) n κs t2
        σ2 Hsteps (by omega)).2

end adequacy
end EtcdGrove
end Perennial

end
