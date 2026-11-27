/- Lean-first (no Rocq counterpart).

The proof of `etcd_restart_robust_single_process.spec` (`Spec/github_com/mit_pdos/etcd_grove/examples/etcd/all/TopLevelRobustness.lean`):
`etcd_restart_safe_single_process` (`Results.lean`) for every execution of fewer than `2 ^ 48` steps, by
`robust_of_single_below_init` (`Robustness.Robust.of_single_below` with the extensions' initial states).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.all.TopLevelRobustness
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.all.Results

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

/-- `etcd_restart_robust_single_process.spec`
(`Spec/github_com/mit_pdos/etcd_grove/examples/etcd/all/TopLevelRobustness.lean`). -/
theorem etcd_restart_robust_single_process : etcd_restart_robust_single_process.spec := by
  intro lctx sem package_sem cache_sem _ k₅ ids₅ ps₅ ctxs₅ boot₅ Hlen₅ Hbf₅ rId ctxsR bootR HbfR Hbg₅ HbgR Hlow
    Haf Hbuq Hdbo HAs HDs HEnv Hfips Hprem₅ σ g Hfs HWal
  exact
    robust_of_single_below_init fun hf hg _ n κs t2 σ2 hn Hsteps =>
      (etcd_restart_safe_single_process
        k₅ ids₅ ps₅ ctxs₅ boot₅ Hlen₅ Hbf₅ rId ctxsR bootR HbfR Hbg₅ HbgR Hlow Haf Hbuq Hdbo HAs HDs HEnv
        Hfips n (Hprem₅ n (by omega)) σ g hg Hfs HWal hf.1 hf.2.1 hf.2.2 κs t2 σ2
        Hsteps (by omega)).2

end adequacy
end EtcdGrove
end Perennial

end
