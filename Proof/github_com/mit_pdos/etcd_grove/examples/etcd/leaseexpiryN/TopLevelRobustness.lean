/- Lean-first (no Rocq counterpart).

# `etcd/leaseexpiryN`: the top-level robustness result, proved

`etcd_leaseexpiryN_robust_single_process`, stated in
`Spec/github_com/mit_pdos/etcd_grove/examples/etcd/leaseexpiryN/TopLevelRobustness.lean`,
from the example's closed theorem (`Results.lean`).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.leaseexpiryN.TopLevelRobustness
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.leaseexpiryN.Results

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

/-- `etcd_leaseexpiryN_robust_single_process.spec`
(`Spec/github_com/mit_pdos/etcd_grove/examples/etcd/leaseexpiryN/TopLevelRobustness.lean`). -/
theorem etcd_leaseexpiryN_robust_single_process : etcd_leaseexpiryN_robust_single_process.spec := by
  intro lctx sem package_sem cache_sem _ _ _ Hctx Hcec k ids ps ctxs boot Hlen Hbf Hap Haf Hbuq
    Hrf Hdbo Hlp HAs HDs HEnv Hprem σ g Hfs HWal
  exact
    robust_of_single_below_init fun hf hg _ n κs t2 σ2 hn Hsteps =>
      (etcd_leaseexpiryN_safe_single_process
        Hctx Hcec k ids ps ctxs boot Hlen Hbf Hap Haf Hbuq Hrf Hdbo Hlp HAs HDs HEnv n
        (Hprem n) σ g hg Hfs HWal hf.1 hf.2.1 hf.2.2 κs t2 σ2 Hsteps (by omega)).2

end adequacy
end EtcdGrove
end Perennial

end
