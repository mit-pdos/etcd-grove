/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/api/v3compactor/Periodic__Resume.lean`. Lean-first (no Rocq
counterpart). The spec-first pilot's phase 1 (`notes/compactor-pilot-plan.md`): the spec is written,
the proof is phase 4's (after the freeze, 2026-10-27).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3compactor.Periodic__Resume

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver.api v3compactor

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3compactor.Assumptions]

theorem v3compactor.Periodic.Resume.wp_proof :
    v3compactor.Periodic.Resume.spec (GF := GF) (hG := hG) := by
  intro pc E period
  wp_start as #Hcp
  iunfold isPeriodic at Hcp
  icases Hcp with ⟨%lg, %clk, %pd, %ctx, %cd, %γctx, %cancel, #Hlg, %Hlgnn, #Hclkf, #Hclk, #Hpdf, %Hpd, #Hrg, #Hc, #Hctxf, #Hctx, #Htrc, #Hcancelf, #Hcs, #Hguard⟩
  wp_auto
  ihave #Psync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  wp_apply sync.RWMutex.wp_Lock_guard $$ [] as ⟨Hlk, HP⟩
  · iframe #
  iunfold perPausedInv at HP
  icases HP with ⟨%b, Hb⟩
  (try wp_auto)
  wp_apply sync.RWMutex.wp_Unlock_guard $$ [$Hlk Hb]
  · iframe #
    inext
    iunfold perPausedInv
    iexists false
    iframe
  (try wp_auto)
  iapply HΦ; itrivial

end proof

end EtcdGrove
end Perennial
