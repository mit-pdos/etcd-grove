/- Lean-first (no Rocq counterpart).

# `k8s/all`: the one closed Kubernetes theorem as a robustness result, proved

`k8s_robust_single_process`, stated in `Spec/github_com/mit_pdos/etcd_grove/examples/k8s/all/TopLevelRobustness.lean`,
from the closed theorem `k8s_safe_single_process` (`Results.lean`).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.all.TopLevelRobustness
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.all.Results

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

attribute [local instance] etcdNetExts etcdNetExtsSemantics etcdNetExtsInterp etcdNetExts_hasIdIssue
  etcdNetExts_hasFs etcdNetExts_hasNet

variable [go_gctx : GoGlobalContext]

/-- `k8s_robust_single_process.spec` (`Spec/github_com/mit_pdos/etcd_grove/examples/k8s/all/TopLevelRobustness.lean`). -/
theorem k8s_robust_single_process : k8s_robust_single_process.spec := by
  intro lctx sem package_sem cache_sem _ _ Hafter k₁ ids ps ctxs boot
    Hlen Hbf k₂ ids' ps' ctxs' boot' Hlen' Hbf' Hlow Haf Hbuq Hrf Hdbo clients ops watchers wops n₁ n₂
    HAs HDs HEnv Hprem₁ Hprem₂ σ g Hfs HWal
  exact
    robust_of_single_below_init fun hf hg _ n κs t2 σ2 hn hexec =>
      (k8s_adequate_below Hafter k₁ ids ps ctxs boot Hlen Hbf k₂ ids' ps' ctxs' boot'
        Hlen' Hbf' Haf Hbuq Hrf Hdbo clients ops watchers wops n₁ n₂ HAs HDs HEnv n
        (Hprem₁ n (by omega)) (Hprem₂ n (by omega)) σ g hg Hfs HWal
        hf.1 hf.2.1 hf.2.2 κs t2 σ2 hexec (by omega)).2

end adequacy
end EtcdGrove
end Perennial

end
