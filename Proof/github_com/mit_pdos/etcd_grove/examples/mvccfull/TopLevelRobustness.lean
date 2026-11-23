/- Lean-first (no Rocq counterpart).

# `mvccfull`: the top-level robustness result, proved

`mvccfull_robust`, stated in
`Spec/github_com/mit_pdos/etcd_grove/examples/mvccfull/TopLevelRobustness.lean`,
from the example's closed theorem (`Results.lean`).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.TopLevelRobustness
public import Proof.github_com.mit_pdos.etcd_grove.examples.mvccfull.Results

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

set_option synthInstance.maxSize 4096

set_option synthInstance.maxHeartbeats 400000

namespace Perennial

namespace EtcdGrove

open Iris Iris.BI

section adequacy

attribute [local instance] etcdFsExts etcdFsExtsSemantics etcdFsExtsInterp etcdFsExts_hasIdIssue
  etcdFsExts_hasFs etcdFsSem etcdFsSemOk etcdFsNoErr

variable [go_gctx : GoGlobalContext]

/-- `mvccfull_robust.spec`
(`Spec/github_com/mit_pdos/etcd_grove/examples/mvccfull/TopLevelRobustness.lean`). -/
theorem mvccfull_robust : mvccfull_robust.spec := by
  intro lctx sem package_sem mvcc_sem srv_sem cache_sem _ _ r HEnv σ g Hfs j0 Hr Habs Hrfit
  exact
    Robustness.Robust.of_single_below fun hf n κs t2 σ2 hn Hsteps =>
      (mvccfull_adequate_below
        r HEnv σ g hf.1 hf.2.1 Hfs j0 Hr Habs Hrfit hf.2.2 (2 ^ 28) (Nat.le_refl _) n κs t2 σ2
        Hsteps (by omega)).2

end adequacy
end EtcdGrove
end Perennial

end
