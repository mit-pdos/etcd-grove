/- Lean-first (no Rocq counterpart).

# `etcd/leaseexpiryN`: the top-level robustness result, proved

`etcd_leaseexpiryN_robust`, stated in
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

attribute [local instance] etcdFsExts etcdFsExtsSemantics etcdFsExtsInterp etcdFsExts_hasIdIssue
  etcdFsExts_hasFs

variable [go_gctx : GoGlobalContext]

/-- `etcd_leaseexpiryN_robust.spec`
(`Spec/github_com/mit_pdos/etcd_grove/examples/etcd/leaseexpiryN/TopLevelRobustness.lean`). -/
theorem etcd_leaseexpiryN_robust : etcd_leaseexpiryN_robust.spec := by
  intro lctx sem package_sem promreg_sem cache_sem _ _ Hctx Hcec k hk1 hk ids ps ctxs boot Hlen Hbf Hap Haf Hbuq
    Hrf Hdbo Hlp HAs HDs HEnv Hprem σ g Hfs HWal
  exact
    Robustness.Robust.of_single_below fun hf n κs t2 σ2 hn Hsteps =>
      (etcd_leaseexpiryN_safe
        Hctx Hcec k hk1 hk ids ps ctxs boot Hlen Hbf Hap Haf Hbuq Hrf Hdbo Hlp HAs HDs HEnv n
        (Hprem n) σ g Hfs HWal hf.1 hf.2.1 hf.2.2 κs t2 σ2 Hsteps (by omega)).2

end adequacy
end EtcdGrove
end Perennial

end
