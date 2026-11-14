/-
Proof of the spec of the same name. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.authMaintenanceServer__Downgrade
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.authMaintenanceServer__isPermitted
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.togRPCError
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.TogRPCErrorPlain

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

theorem v3rpc.authMaintenanceServer.Downgrade.wp_proof
    (hG0 : v3rpc.authMaintenanceServer.isPermitted.specC (GF := GF) (hG := hG))
    (hTog : v3rpc.togRPCError.spec (GF := GF) (hG := hG)) :
    v3rpc.authMaintenanceServer.Downgrade.spec (GF := GF) (hG := hG) := by
  intro p ms aa s E ctx cd r Pin Q n
  wp_start as ⟨#Hams, #Haa, #Hlb, #Hctx, #Hlib, HRD, HPin, #Hin⟩
  ihave #Hams' := Hams
  iunfold v3rpc.amsIs at Hams'
  icases Hams' with ⟨%Hpn, #Hms, #Haaf⟩
  (try wp_auto)
  wp_apply (hG0 p ms aa s E ctx cd n) $$ [$HRD] as %err ⟨HRD, #HoutC⟩
  · iframe #
  ihave #Hout := adminOut_of_C _ _ _ _ _ $$ HoutC
  iunfold adminOut at Hout
  icases Hout with ⟨#Herr, #Htok⟩
  (try wp_auto)
  rcases err with ei | _
  · (try wp_auto)
    wp_apply (v3rpc.togRPCError_out hTog) $$ [] as %e ⟨%He, -, #Hgo⟩
    · iframe #
      iapply (v3rpc.srvErrIs_applyErrIs (GoInterface.ok ei) (by intro h; cases h)) $$ Herr
    (try wp_auto)
    iapply HΦ
    iframe HRD
    iapply (v3rpc.guardOutC_guard Pin Q _ (GoInterface.ok ei) e (fun h => by cases h) He)
    iframe HPin Hgo
    iunfold adminOutC at HoutC
    icases HoutC with ⟨-, #Hw⟩
    iapply Hw; intro h; cases h
  · (try wp_auto)
    ispecialize Htok $$ %rfl
    icases Htok with ⟨%ai, #Htk⟩
    iunfold v3rpc.guardedOk2 at Hin
    ispecialize Hin $$ %ai
    wp_apply Hin $$ [$HPin $HRD] as %resp %err2 ⟨HRD, HQ⟩
    · iframe #
    (try wp_auto)
    iapply HΦ
    iframe HRD
    iunfold v3rpc.guardOutC
    ileft
    iexact HQ

end proof

end EtcdGrove
end Perennial
