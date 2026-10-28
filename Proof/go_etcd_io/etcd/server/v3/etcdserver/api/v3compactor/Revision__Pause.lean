/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/api/v3compactor/Revision__Pause.lean`. Lean-first (no Rocq
counterpart). The spec-first pilot's phase 1 (`notes/compactor-pilot-plan.md`): the spec is written,
the proof is phase 4's (after the freeze, 2026-10-27).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3compactor.Revision__Pause

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

theorem v3compactor.Revision.Pause.wp_proof :
    v3compactor.Revision.Pause.spec (GF := GF) (hG := hG) := by
  intro rc E ret
  wp_start as #Hcp
  iunfold isRevision at Hcp
  icases Hcp with ⟨%lg, %clk, %rt, %ctx, %cd, %γctx, %cancel, #Hlg, %Hlgnn, #Hclkf, #Hclk, #Hrt, %Hrt, #Hrg, #Hc, #Hctxf, #Hctx, #Hcancelf, #Hcs, #Hmu⟩
  wp_auto
  wp_apply sync.Mutex.wp_Lock $$ [$Hmu] as ⟨Hlocked, Hinv⟩
  iunfold revPausedInv at Hinv
  icases Hinv with ⟨%pz, Hpz⟩
  (try wp_auto)
  wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked Hpz]
  · inext; iunfold revPausedInv; iexists true; iframe
  (try wp_auto)
  iapply HΦ; itrivial

end proof

end EtcdGrove
end Perennial
