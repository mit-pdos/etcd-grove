/- Lean-first (no Rocq counterpart).

# `etcd/lease`: the top-level robustness result, proved

`etcd_lease_robust`, stated in
`Spec/github_com/mit_pdos/etcd_grove/examples/etcd/lease/TopLevelRobustness.lean`,
from the example's closed theorem (`Results.lean`).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.lease.TopLevelRobustness
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.lease.Results

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

/-- `etcd_lease_robust.spec`
(`Spec/github_com/mit_pdos/etcd_grove/examples/etcd/lease/TopLevelRobustness.lean`). -/
theorem etcd_lease_robust : etcd_lease_robust.spec := by
  intro lctx sem package_sem cache_sem _ _ Hctx Hcec id ctxs boot Hbf Haf Hbuq Hrf Hdbo Hlp HNs HAs
    HDs HEnv Hprem σ g Hfs HWal
  exact
    Robustness.Robust.of_single fun hf n κs t2 σ2 hn Hsteps =>
      (etcd_lease_safe
        Hctx Hcec id ctxs boot Hbf Haf Hbuq Hrf Hdbo Hlp HNs HAs HDs HEnv n (Hprem n (by omega)) σ g
        Hfs HWal hf.1 hf.2.1 hf.2.2 κs t2 σ2 Hsteps (by omega)).2

end adequacy
end EtcdGrove
end Perennial

end
