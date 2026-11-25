/- Lean-first (no Rocq counterpart).

The proof of `etcd_robust_single_process.spec` (`Spec/github_com/mit_pdos/etcd_grove/examples/etcd/all/TopLevelRobustness.lean`):
`etcd_safe_single_process` (`Results.lean`) for every execution of fewer than `2 ^ 48` steps, by
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

/-- `etcd_robust_single_process.spec`
(`Spec/github_com/mit_pdos/etcd_grove/examples/etcd/all/TopLevelRobustness.lean`). -/
theorem etcd_robust_single_process : etcd_robust_single_process.spec := by
  intro lctx sem package_sem _ _ _ _ _ k₁ ids₁ ps₁ ctxs₁ boot₁ Hlen₁
    Hbf₁ pid₁ pid₂ pid₃ psP ctxsP bootP HbfP cwId ctxsCW bootCW HbfCW cId ctxsC bootC HbfC kvId ctxsK
    bootK HbfK k₂ ids₂ ps₂ ctxs₂ boot₂ Hlen₂ Hbf₂ k₃ ids₃ ps₃ ctxs₃ boot₃ Hlen₃ Hbf₃
    Hap k₄ ids₄ ps₄ ctxs₄ boot₄ Hlen₄ Hbf₄ lid₁ lid₂ lid₃ psL ctxsL bootL HbfL k₅
    ids₅ ps₅ ctxs₅ boot₅ Hlen₅ Hbf₅ rId ctxsR bootR HbfR Hlow Haf Hbuq Hrf Hdbo Hlp Hlne clients ops
    n₁ nw nops n₂ cnw cnops HAs HDs HEnv Hprem₁ HpremP HpremCW HpremC HpremK Hprem₂ Hprem₃ Hprem₄
    HpremL Hprem₅ HpremR σ g Hfs HWal
  exact
    robust_of_single_below_init fun hf hg _ n κs t2 σ2 hn Hsteps =>
      (etcd_safe_single_process
        k₁ ids₁ ps₁ ctxs₁ boot₁ Hlen₁ Hbf₁ pid₁ pid₂ pid₃ psP ctxsP bootP HbfP
        cwId ctxsCW bootCW HbfCW cId ctxsC bootC HbfC kvId ctxsK bootK HbfK k₂ ids₂ ps₂
        ctxs₂ boot₂ Hlen₂ Hbf₂ k₃ ids₃ ps₃ ctxs₃ boot₃ Hlen₃ Hbf₃ Hap k₄ ids₄ ps₄
        ctxs₄ boot₄ Hlen₄ Hbf₄ lid₁ lid₂ lid₃ psL ctxsL bootL HbfL k₅ ids₅ ps₅ ctxs₅ boot₅
        Hlen₅ Hbf₅ rId ctxsR bootR HbfR Hlow Haf Hbuq Hrf Hdbo Hlp Hlne clients ops n₁ nw nops n₂
        cnw cnops HAs HDs HEnv n (Hprem₁ n (by omega)) (HpremP n (by omega)) (HpremCW n (by
        omega)) (HpremC n (by omega)) (HpremK n (by omega)) (Hprem₂ n (by omega)) (Hprem₃ n (by
        omega)) (Hprem₄ n (by omega)) (HpremL n (by omega)) (Hprem₅ n (by omega)) (HpremR n (by
        omega)) σ g hg Hfs HWal hf.1 hf.2.1 hf.2.2 κs t2 σ2 Hsteps (by omega)).2

end adequacy
end EtcdGrove
end Perennial

end
