/-
Proof of `Spec/go_etcd_io/etcd/pkg/v3/traceutil/Trace__LogWithStepThreshold.lean`: `logInfo`, then
`t.lg.Info` if the logger is not nil (a zap logger: `zapLoggerOrNil`). Lean-first (no Rocq
counterpart); traceutil-log (2026-11-23; until then a trust-boundary axiom, unit P1b, when `logInfo`
was names-only).
-/
module

public import Spec.go_etcd_io.etcd.pkg.v3.traceutil.Trace__LogWithStepThreshold
public import Spec.go_etcd_io.etcd.pkg.v3.traceutil.Trace__logInfo
public import Spec.go_uber_org.zap.Logger__Info

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode _root_.Perennial.go_etcd_io.etcd.pkg.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.pkg.v3.traceutil.Assumptions]

theorem traceutil.Trace.LogWithStepThreshold.wp_proof
    (hLog : traceutil.Trace.logInfo.spec (GF := GF) (hG := hG))
    (hInfo : zap.Logger.Info.spec (GF := GF) (hG := hG)) :
    traceutil.Trace.LogWithStepThreshold.spec (GF := GF) (hG := hG) := by
  intro t e d
  wp_start as Ht
  ihave #Pzap : isPkgInit (PROP := IProp GF) pkg_id.go_uber_org.zap $$ []
  · iPkgInit
  wp_auto
  wp_apply hLog t e d $$ [Ht] as %msg %fs ⟨%v, Ht, #Hlz⟩
  · iframe #
    iframe
  (try wp_auto)
  wp_if_destruct
  · (try wp_auto)
    iapply HΦ
    itrivial
  · ihave #Hl := zapLoggerOrNil_ok _ (by simpa using Hif) $$ Hlz
    wp_apply hInfo v.lg' msg fs $$ []
    · iframe #
    (try wp_auto)
    iapply HΦ
    itrivial

end proof

end EtcdGrove
end Perennial
