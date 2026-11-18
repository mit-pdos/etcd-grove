/- Lean-first (no Rocq counterpart).

# `etcd/partition`: the top-level robustness results, proved

`etcd_partition_robust`, `etcd_partition_watch_robust`, stated in
`Spec/github_com/mit_pdos/etcd_grove/examples/etcd/partition/TopLevelRobustness.lean`,
from the example's closed theorems (`Results.lean`).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.partition.TopLevelRobustness

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

/-- `etcd_partition_robust.spec`
(`Spec/github_com/mit_pdos/etcd_grove/examples/etcd/partition/TopLevelRobustness.lean`). -/
theorem etcd_partition_robust : etcd_partition_robust.spec := by
  intro lctx sem package_sem cache_sem _ _ Hctx Hcec id₁ id₂ id₃ ps ctxs boot Hbf Haf Hbuq Hrf Hdbo
    clients ops Hc0 Hc31 Hops Hmul steps Hsteps HNs HAs HDs HEnv Hprem σ g Hfs
  exact
    Robustness.Robust.of_single fun hf n κs t2 σ2 hn hexec =>
      (etcd_partition_safe
        Hctx Hcec id₁ id₂ id₃ ps ctxs boot Hbf Haf Hbuq Hrf Hdbo clients ops Hc0 Hc31 Hops Hmul
        steps Hsteps HNs HAs HDs HEnv n (Hprem n (by omega)) σ g Hfs hf.1 hf.2.1 hf.2.2 κs t2 σ2
        hexec (by omega)).2

/-- `etcd_partition_watch_robust.spec`
(`Spec/github_com/mit_pdos/etcd_grove/examples/etcd/partition/TopLevelRobustness.lean`). -/
theorem etcd_partition_watch_robust : etcd_partition_watch_robust.spec := by
  intro lctx sem package_sem cache_sem _ _ _ _ _ Hctx Hcec id₁ id₂ id₃ ps ctxs boot Hbf Haf Hbuq Hrf
    Hdbo nw nops H0 H31 Hops Hmul steps Hsteps HNs HAs HDs HEnv Hprem σ g Hfs
  exact
    Robustness.Robust.of_single fun hf n κs t2 σ2 hn hexec =>
      (etcd_partition_watch_safe
        Hctx Hcec id₁ id₂ id₃ ps ctxs boot Hbf Haf Hbuq Hrf Hdbo nw nops H0 H31 Hops Hmul steps
        Hsteps HNs HAs HDs HEnv n (Hprem n (by omega)) σ g Hfs hf.1 hf.2.1 hf.2.2 κs t2 σ2 hexec
        (by omega)).2

end adequacy
end EtcdGrove
end Perennial

end
