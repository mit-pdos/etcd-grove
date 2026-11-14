/-
Proof of the spec of the same name. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.authMaintenanceServer__isPermitted
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.AuthAdmin__isPermitted
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

theorem v3rpc.authMaintenanceServer.isPermitted.wp_proofC
    (hP : v3rpc.AuthAdmin.isPermitted.specC (GF := GF) (hG := hG)) :
    v3rpc.authMaintenanceServer.isPermitted.specC (GF := GF) (hG := hG) := by
  intro p ms aa s E ctx cd n
  wp_start as ⟨#Hams, #Haa, #Hlb, #Hctx, #Hlib, HRD⟩
  iunfold v3rpc.amsIs at Hams
  icases Hams with ⟨%Hpn, #Hms, #Haaf⟩
  (try wp_auto)
  wp_apply (hP aa s E ctx cd n) $$ [$HRD] as %err ⟨HRD, #Hout⟩
  · iframe #
  (try wp_auto)
  iapply HΦ
  iframe HRD Hout

/-- `spec`, of `specC` (auth-guard-completeness G2): the reason dropped, at the lower bound `0`
(`authPubLbM_zero`). -/
theorem v3rpc.authMaintenanceServer.isPermitted.wp_proof
    (hP : v3rpc.AuthAdmin.isPermitted.specC (GF := GF) (hG := hG)) :
    v3rpc.authMaintenanceServer.isPermitted.spec (GF := GF) (hG := hG) := by
  intro p ms aa s E ctx cd
  iintro %Φ ⟨#Hpkg, #Hams, #Haa, -, #Hctx, #Hlib, HRD⟩ HΦ
  imod (authPubLbM_zero (GF := GF) E.authMode) with #Hn
  iapply (v3rpc.authMaintenanceServer.isPermitted.wp_proofC hP p ms aa s E ctx cd 0) $$ [HRD]
  · iframe; iframe #
  iintro !> %err ⟨HRD, #Hout⟩
  iapply HΦ
  iframe HRD
  iapply adminOut_of_C $$ Hout

end proof

end EtcdGrove
end Perennial
