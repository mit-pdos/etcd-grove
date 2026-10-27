/-
Proof of the spec of the same name. Lean-first (no Rocq counterpart); unit P4 (2026-10-14).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.txn.warnOfExpensiveGenericRequest
public import Spec.go_uber_org.zap.Duration
public import Spec.go_uber_org.zap.String
public import Spec.go_uber_org.zap.Error
public import Spec.go_uber_org.zap.Logger__Warn

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.txn.Assumptions]

theorem txn.warnOfExpensiveGenericRequest.wp_proof
    (hDur : zap.Duration.spec (GF := GF) (hG := hG))
    (hStr : zap.String.spec (GF := GF) (hG := hG))
    (hErr : zap.Error.spec (GF := GF) (hG := hG))
    (hWarn : zap.Logger.Warn.spec (GF := GF) (hG := hG)) :
    txn.warnOfExpensiveGenericRequest.spec (GF := GF) (hG := hG) := by
  intro lg d now req pfx resp err
  wp_start as ⟨%Hlg, #Hs⟩
  iunfold txn.stringerOk at Hs
  icases Hs with ⟨%si, %Hsi, #HS⟩
  subst Hsi
  ihave Hinit : (go_etcd_io.etcd.server.v3.etcdserver.txn.txnInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  icases Hinit with ⟨-, -, ⟨%c, #Hc, #Hcs⟩⟩
  (try wp_auto)
  wp_apply time.wp_Since as %_ -
  wp_apply hDur as %_ -
  wp_apply hDur as %_ -
  wp_apply hStr as %_ -
  wp_apply HS as %_ -
  wp_apply hStr as %_ -
  wp_apply hStr as %_ -
  wp_apply hErr as %_ -
  wp_apply wp_slice_literal
  isplitr
  · ipureintro; rfl
  iintro %_ ⟨-, -⟩
  (try wp_auto)
  wp_apply hWarn
  · ipureintro; exact Hlg
  (try wp_auto)
  iunfold go_etcd_io.etcd.server.v3.lease.counterSpec at Hcs
  wp_apply Hcs
  (try wp_auto)
  iapply HΦ
  itrivial

end proof

end EtcdGrove
end Perennial
