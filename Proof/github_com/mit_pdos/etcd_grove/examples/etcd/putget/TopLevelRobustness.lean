/- Lean-first (no Rocq counterpart).

# `etcd/putget`: the top-level robustness result, proved

`etcd_putget_robust`, stated in
`Spec/github_com/mit_pdos/etcd_grove/examples/etcd/putget/TopLevelRobustness.lean`,
from the example's closed theorem (`Results.lean`).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.putget.TopLevelRobustness
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.putget.Results

@[expose] public section

noncomputable section

set_option pp.fullNames true

set_option linter.unusedSectionVars false

set_option synthInstance.maxSize 4096

set_option synthInstance.maxHeartbeats 400000

namespace Perennial

namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section adequacy

attribute [local instance] etcdFsExts etcdFsExtsSemantics etcdFsExtsInterp etcdFsExts_hasIdIssue
  etcdFsExts_hasFs

variable [go_gctx : GoGlobalContext]

/-- `etcd_putget_robust.spec`
(`Spec/github_com/mit_pdos/etcd_grove/examples/etcd/putget/TopLevelRobustness.lean`). -/
theorem etcd_putget_robust : etcd_putget_robust.spec := by
  intro lctx sem package_sem cache_sem _ _ Hctx Hcec id ctxs boot Hbf Haf Hbuq Hrf Hdbo HNs HAs HDs
    HEnv Hprem σ g Hfs
  exact
    Robustness.Robust.of_single fun hf n κs t2 σ2 hn Hsteps =>
      (etcd_putget_safe
        Hctx Hcec id ctxs boot Hbf Haf Hbuq Hrf Hdbo HNs HAs HDs HEnv n (Hprem n (by omega)) σ g Hfs
        hf.1 hf.2.1 hf.2.2 κs t2 σ2 Hsteps (by omega)).2

end adequacy
end EtcdGrove
end Perennial

end
