/- Lean-first (no Rocq counterpart).

# `k8s/compactor`: the top-level robustness results, proved

`k8s_compactor_robust`, `k8s_compactor_partition_robust`, stated in
`Spec/github_com/mit_pdos/etcd_grove/examples/k8s/compactor/TopLevelRobustness.lean`,
from the example's closed theorems (`Results.lean`).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.compactor.TopLevelRobustness
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.compactor.Results

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

/-- `k8s_compactor_robust.spec`
(`Spec/github_com/mit_pdos/etcd_grove/examples/k8s/compactor/TopLevelRobustness.lean`). -/
theorem k8s_compactor_robust : k8s_compactor_robust.spec := by
  intro lctx sem package_sem cache_sem _ _ Hctx Hcec id ctxs boot Hbf Haf Hbuq Hrf Hdbo HNs HAs HDs
    HEnv Hprem Hafter σ g Hfs HWal
  exact
    Robustness.Robust.of_single fun hf n κs t2 σ2 hn hexec =>
      (k8s_compactor_safe
        Hctx Hcec id ctxs boot Hbf Haf Hbuq Hrf Hdbo HNs HAs HDs HEnv n (Hprem n (by omega)) Hafter
        σ g Hfs HWal hf.1 hf.2.1 hf.2.2 κs t2 σ2 hexec (by omega)).2

/-- `k8s_compactor_partition_robust.spec`
(`Spec/github_com/mit_pdos/etcd_grove/examples/k8s/compactor/TopLevelRobustness.lean`). -/
theorem k8s_compactor_partition_robust : k8s_compactor_partition_robust.spec := by
  intro lctx sem package_sem cache_sem _ _ Hctx Hcec id₁ id₂ id₃ ps ctxs boot Hbf Haf Hbuq Hrf Hdbo
    steps Hsteps HNs HAs HDs HEnv Hprem Hafter σ g Hfs HWal
  exact
    Robustness.Robust.of_single fun hf n κs t2 σ2 hn hexec =>
      (k8s_compactor_partition_safe
        Hctx Hcec id₁ id₂ id₃ ps ctxs boot Hbf Haf Hbuq Hrf Hdbo steps Hsteps HNs HAs HDs HEnv n
        (Hprem n (by omega)) Hafter σ g Hfs HWal hf.1 hf.2.1 hf.2.2 κs t2 σ2 hexec (by omega)).2

end adequacy
end EtcdGrove
end Perennial

end
