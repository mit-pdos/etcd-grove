/- Lean-first (no Rocq counterpart).

# `etcd/txnlinfaultsN`: the top-level robustness result, proved

`etcd_txnlinfaultsN_robust`, stated in
`Spec/github_com/mit_pdos/etcd_grove/examples/etcd/txnlinfaultsN/TopLevelRobustness.lean`,
from the example's closed theorem (`Results.lean`).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.txnlinfaultsN.TopLevelRobustness
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.txnlinfaultsN.Results

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

/-- `etcd_txnlinfaultsN_robust.spec`
(`Spec/github_com/mit_pdos/etcd_grove/examples/etcd/txnlinfaultsN/TopLevelRobustness.lean`). -/
theorem etcd_txnlinfaultsN_robust : etcd_txnlinfaultsN_robust.spec := by
  intro lctx sem package_sem cache_sem _ _ Hctx Hcec k hk1 hk ids ps ctxs boot Hlen Hbf Haf Hbuq Hrf
    Hdbo clients ops Hc0 Hc31 Hops Hmul steps Hsteps HNs HAs HDs HEnv Hprem σ g Hfs HWal
  exact
    Robustness.Robust.of_single_below fun hf n κs t2 σ2 hn hexec =>
      (etcd_txnlinfaultsN_safe
        Hctx Hcec k hk1 hk ids ps ctxs boot Hlen Hbf Haf Hbuq Hrf Hdbo clients ops Hc0 Hc31 Hops
        Hmul steps Hsteps HNs HAs HDs HEnv n (Hprem n) σ g Hfs HWal hf.1 hf.2.1 hf.2.2 κs t2
        σ2 hexec (by omega)).2

end adequacy
end EtcdGrove
end Perennial

end
