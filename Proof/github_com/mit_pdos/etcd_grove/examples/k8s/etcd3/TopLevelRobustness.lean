/- Lean-first (no Rocq counterpart).

# `k8s/etcd3`: the top-level robustness results, proved

`k8s_etcd3_robust`, `k8s_etcd3_cluster_robust`, `k8s_etcd3_partition_robust`, stated in
`Spec/github_com/mit_pdos/etcd_grove/examples/k8s/etcd3/TopLevelRobustness.lean`,
from the example's closed theorems (`Results.lean`).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.TopLevelRobustness

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

/-- `k8s_etcd3_robust.spec`
(`Spec/github_com/mit_pdos/etcd_grove/examples/k8s/etcd3/TopLevelRobustness.lean`). -/
theorem k8s_etcd3_robust : k8s_etcd3_robust.spec := by
  intro lctx sem package_sem cache_sem _ _ _ _ _ _ _ Hctx Hcec id ctxs boot Hbf Haf Hbuq Hrf Hdbo
    clients ops watchers wops Hc0 Hw0 Hc31 Hops Hwops Hmul HNs HAs HDs HEnv Hprem σ g Hfs
  exact
    Robustness.Robust.of_single fun hf n κs t2 σ2 hn hexec =>
      (k8s_etcd3_safe
        Hctx Hcec id ctxs boot Hbf Haf Hbuq Hrf Hdbo clients ops watchers wops Hc0 Hw0 Hc31 Hops
        Hwops Hmul HNs HAs HDs HEnv n (Hprem n (by omega)) σ g Hfs hf.1 hf.2.1 hf.2.2 κs t2 σ2 hexec
        (by omega)).2

/-- `k8s_etcd3_cluster_robust.spec`
(`Spec/github_com/mit_pdos/etcd_grove/examples/k8s/etcd3/TopLevelRobustness.lean`). -/
theorem k8s_etcd3_cluster_robust : k8s_etcd3_cluster_robust.spec := by
  intro lctx sem package_sem cache_sem _ _ _ _ _ _ _ Hctx Hcec k hk1 hk ids ps ctxs boot Hlen Hbf
    Haf Hbuq Hrf Hdbo clients ops watchers wops Hc0 Hw0 Hc31 Hops Hwops Hmul HNs HAs HDs HEnv Hprem
    σ g Hfs
  exact
    Robustness.Robust.of_single fun hf n κs t2 σ2 hn hexec =>
      (k8s_etcd3_cluster_safe
        Hctx Hcec k hk1 hk ids ps ctxs boot Hlen Hbf Haf Hbuq Hrf Hdbo clients ops watchers wops Hc0
        Hw0 Hc31 Hops Hwops Hmul HNs HAs HDs HEnv n (Hprem n (by omega)) σ g Hfs hf.1 hf.2.1 hf.2.2
        κs t2 σ2 hexec (by omega)).2

/-- `k8s_etcd3_partition_robust.spec`
(`Spec/github_com/mit_pdos/etcd_grove/examples/k8s/etcd3/TopLevelRobustness.lean`). -/
theorem k8s_etcd3_partition_robust : k8s_etcd3_partition_robust.spec := by
  intro lctx sem package_sem cache_sem _ _ _ _ _ _ _ Hctx Hcec k hk1 hk ids ps ctxs boot Hlen Hbf
    Haf Hbuq Hrf Hdbo clients ops watchers wops Hc0 Hw0 Hc31 Hops Hwops Hmul steps Hsteps HNs HAs
    HDs HEnv Hprem σ g Hfs
  exact
    Robustness.Robust.of_single fun hf n κs t2 σ2 hn hexec =>
      (k8s_etcd3_partition_safe
        Hctx Hcec k hk1 hk ids ps ctxs boot Hlen Hbf Haf Hbuq Hrf Hdbo clients ops watchers wops Hc0
        Hw0 Hc31 Hops Hwops Hmul steps Hsteps HNs HAs HDs HEnv n (Hprem n (by omega)) σ g Hfs hf.1
        hf.2.1 hf.2.2 κs t2 σ2 hexec (by omega)).2

end adequacy
end EtcdGrove
end Perennial

end
