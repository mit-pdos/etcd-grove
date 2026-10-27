/-
Proof of the spec of the same name. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.authMaintenanceServer__Snapshot
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.authMaintenanceServer__isPermitted
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
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

theorem v3rpc.authMaintenanceServer.Snapshot.wp_proof
    (hP : v3rpc.authMaintenanceServer.isPermitted.spec (GF := GF) (hG := hG))
    (hTog : v3rpc.togRPCError.spec (GF := GF) (hG := hG)) :
    v3rpc.authMaintenanceServer.Snapshot.spec (GF := GF) (hG := hG) := by
  intro p ms aa s E ctx cd sr srv Pin Q
  wp_start as ⟨#Hams, #Haa, #Hnil, #Hctx, HRD, HPin, #Hsc, #Hin⟩
  ihave #Hams' := Hams
  iunfold v3rpc.amsIs at Hams'
  icases Hams' with ⟨%Hpn, #Hms, #Haaf⟩
  iunfold v3rpc.streamCtxOk at Hsc
  icases Hsc with ⟨%si, %Hsi, #HCtx⟩
  subst Hsi
  (try wp_auto)
  wp_apply HCtx $$ [] as %c %Hc
  subst Hc
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
    iunfold v3rpc.guardOut1
    iright
    iframe HPin
    ipureintro; exact He
  · (try wp_auto)
    ispecialize Htok $$ %rfl
    icases Htok with ⟨%ai, #Htk⟩
    iunfold v3rpc.guardedSnapOk at Hin
    ispecialize Hin $$ %ai
    wp_apply Hin $$ [$HPin $HRD] as %err2 ⟨HRD, HQ⟩
    · iframe #
    (try wp_auto)
    iapply HΦ
    iframe HRD
    iunfold v3rpc.guardOut1
    ileft
    iexact HQ

end proof

end EtcdGrove
end Perennial
