/-
Proof of the spec of the same name. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.authMaintenanceServer__Alarm
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.authMaintenanceServer__isPermitted
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.authMaintenanceServer__requireAuthInfo
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.togRPCError

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver.api
  go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.etcd.api.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

theorem v3rpc.authMaintenanceServer.Alarm.wp_proof
    (hP : v3rpc.authMaintenanceServer.isPermitted.spec (GF := GF) (hG := hG))
    (hR : v3rpc.authMaintenanceServer.requireAuthInfo.spec (GF := GF) (hG := hG))
    (hTog : v3rpc.togRPCError.spec (GF := GF) (hG := hG)) :
    v3rpc.authMaintenanceServer.Alarm.spec (GF := GF) (hG := hG) := by
  intro p ms aa s E ctx cd ar act Pin Q
  wp_start as ⟨#Hams, #Haa, #Hnil, #Hctx, HRD, HPin, #Hact, #Hin⟩
  ihave #Hams' := Hams
  iunfold v3rpc.amsIs at Hams'
  icases Hams' with ⟨%Hpn, #Hms, #Haaf⟩
  iunfold v3rpc.alarmActionOk at Hact
  (try wp_auto)
  wp_apply Hact $$ [] as %a %Ha
  subst Ha
  (try wp_auto)
  by_cases hact : a = W32 0
  · rw [_root_.decide_eq_true hact]
    (try wp_auto)
    wp_apply (hR p ms aa s E ctx cd) $$ [$HRD] as %err ⟨HRD, #Hout⟩
    · iframe #
    iunfold authedOut at Hout
    icases Hout with ⟨#Herr, -, #Htok, -⟩
    (try wp_auto)
    rcases err with ei | _
    · (try wp_auto)
      wp_apply hTog $$ [] as %e %He
      · iframe #
        iapply (v3rpc.srvErrIs_applyErrIs (GoInterface.ok ei) (by intro h; cases h)) $$ Herr
      (try wp_auto)
      iapply HΦ
      iframe HRD
      iunfold v3rpc.guardOut
      iright
      iframe HPin
      ipureintro; exact ⟨rfl, He⟩
    · (try wp_auto)
      ispecialize Htok $$ %rfl
      icases Htok with ⟨%ai, #Htk⟩
      iunfold v3rpc.guardedOk2 at Hin
      ispecialize Hin $$ %ai
      wp_apply Hin $$ [$HPin $HRD] as %resp %err2 ⟨HRD, HQ⟩
      · iframe #
        simp only [v3rpc.alarmTok, hact, ↓reduceIte]
        iexact Htk
      (try wp_auto)
      iapply HΦ
      iframe HRD
      iunfold v3rpc.guardOut
      ileft
      iexact HQ
  · rw [_root_.decide_eq_false hact]
    (try wp_auto)
    wp_apply (hP p ms aa s E ctx cd) $$ [$HRD] as %err ⟨HRD, #Hout⟩
    · iframe #
    iunfold adminOut at Hout
    icases Hout with ⟨#Herr, #Htok⟩
    (try wp_auto)
    rcases err with ei | _
    · (try wp_auto)
      wp_apply hTog $$ [] as %e %He
      · iframe #
        iapply (v3rpc.srvErrIs_applyErrIs (GoInterface.ok ei) (by intro h; cases h)) $$ Herr
      (try wp_auto)
      iapply HΦ
      iframe HRD
      iunfold v3rpc.guardOut
      iright
      iframe HPin
      ipureintro; exact ⟨rfl, He⟩
    · (try wp_auto)
      ispecialize Htok $$ %rfl
      icases Htok with ⟨%ai, #Htk⟩
      iunfold v3rpc.guardedOk2 at Hin
      ispecialize Hin $$ %ai
      wp_apply Hin $$ [$HPin $HRD] as %resp %err2 ⟨HRD, HQ⟩
      · iframe #
        simp only [v3rpc.alarmTok, hact, ↓reduceIte]
        iexact Htk
      (try wp_auto)
      iapply HΦ
      iframe HRD
      iunfold v3rpc.guardOut
      ileft
      iexact HQ

end proof

end EtcdGrove
end Perennial
