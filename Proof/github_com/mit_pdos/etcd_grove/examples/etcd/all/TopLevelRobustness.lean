/- Lean-first (no Rocq counterpart).

The proof of `etcd_robust.spec` (`Spec/github_com/mit_pdos/etcd_grove/examples/etcd/all/TopLevelRobustness.lean`):
`etcd_safe` (`Results.lean`) for every execution of fewer than `2 ^ 40 - 11` steps, by
`Robustness.Robust.of_single_below`.
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

attribute [local instance] etcdFsExts etcdFsExtsSemantics etcdFsExtsInterp etcdFsExts_hasIdIssue
  etcdFsExts_hasFs

variable [go_gctx : GoGlobalContext]

/-- `etcd_robust.spec`
(`Spec/github_com/mit_pdos/etcd_grove/examples/etcd/all/TopLevelRobustness.lean`). -/
theorem etcd_robust : etcd_robust.spec := by
  intro lctx sem package_sem promreg_sem cache_sem _ _ _ _ _ Hctx Hcec k₁ hk₁1 hk₁ ids₁ ps₁ ctxs₁ boot₁ Hlen₁
    Hbf₁ pid₁ pid₂ pid₃ psP ctxsP bootP HbfP cwId ctxsCW bootCW HbfCW cId ctxsC bootC HbfC kvId ctxsK
    bootK HbfK k₂ hk₂1 hk₂ ids₂ ps₂ ctxs₂ boot₂ Hlen₂ Hbf₂ k₃ hk₃1 hk₃ ids₃ ps₃ ctxs₃ boot₃ Hlen₃ Hbf₃
    Hap k₄ hk₄1 hk₄ ids₄ ps₄ ctxs₄ boot₄ Hlen₄ Hbf₄ lid₁ lid₂ lid₃ psL ctxsL bootL HbfL k₅ hk₅3 hk₅
    ids₅ ps₅ ctxs₅ boot₅ Hlen₅ Hbf₅ rId ctxsR bootR HbfR Hlow Haf Hbuq Hrf Hdbo Hlp Hlne clients ops
    Hc0 Hc31 Hops Hmul steps₁ Hsteps₁ nw nops Hnw0 Hnw31 Hnops Hnmul steps₂ Hsteps₂ cnw cnops Hcnw0
    Hcnw31 Hcnops Hcmul HAs HDs HEnv Hprem₁ HpremP HpremCW HpremC HpremK Hprem₂ Hprem₃ Hprem₄
    HpremL Hprem₅ HpremR σ g Hfs HWal
  exact
    Robustness.Robust.of_single_below fun hf n κs t2 σ2 hn Hsteps =>
      (etcd_safe
        Hctx Hcec k₁ hk₁1 hk₁ ids₁ ps₁ ctxs₁ boot₁ Hlen₁ Hbf₁ pid₁ pid₂ pid₃ psP ctxsP bootP HbfP
        cwId ctxsCW bootCW HbfCW cId ctxsC bootC HbfC kvId ctxsK bootK HbfK k₂ hk₂1 hk₂ ids₂ ps₂
        ctxs₂ boot₂ Hlen₂ Hbf₂ k₃ hk₃1 hk₃ ids₃ ps₃ ctxs₃ boot₃ Hlen₃ Hbf₃ Hap k₄ hk₄1 hk₄ ids₄ ps₄
        ctxs₄ boot₄ Hlen₄ Hbf₄ lid₁ lid₂ lid₃ psL ctxsL bootL HbfL k₅ hk₅3 hk₅ ids₅ ps₅ ctxs₅ boot₅
        Hlen₅ Hbf₅ rId ctxsR bootR HbfR Hlow Haf Hbuq Hrf Hdbo Hlp Hlne clients ops Hc0 Hc31 Hops
        Hmul steps₁ Hsteps₁ nw nops Hnw0 Hnw31 Hnops Hnmul steps₂ Hsteps₂ cnw cnops Hcnw0 Hcnw31
        Hcnops Hcmul HAs HDs HEnv n (Hprem₁ n (by omega)) (HpremP n (by omega)) (HpremCW n (by
        omega)) (HpremC n (by omega)) (HpremK n (by omega)) (Hprem₂ n (by omega)) (Hprem₃ n (by
        omega)) (Hprem₄ n (by omega)) (HpremL n (by omega)) (Hprem₅ n (by omega)) (HpremR n (by
        omega)) σ g Hfs HWal hf.1 hf.2.1 hf.2.2 κs t2 σ2 Hsteps (by omega)).2

end adequacy
end EtcdGrove
end Perennial

end
