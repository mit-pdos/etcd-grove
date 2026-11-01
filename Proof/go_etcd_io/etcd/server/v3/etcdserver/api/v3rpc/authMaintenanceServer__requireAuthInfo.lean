/-
Proof of the spec of the same name. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.authMaintenanceServer__requireAuthInfo
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.AuthAdmin__requireAuthInfo
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

/-- One proof for both modes (the auth-mode merge, 2026-10-29: the former `wp_proof` and
(`requireAuthInfo_bound`)). -/
theorem v3rpc.authMaintenanceServer.requireAuthInfo.wp_proof
    (hP : v3rpc.AuthAdmin.requireAuthInfo.spec (GF := GF) (hG := hG)) :
    v3rpc.authMaintenanceServer.requireAuthInfo.spec (GF := GF) (hG := hG) := by
  intro p ms aa s E ctx cd
  wp_start as ⟨#Hams, #Haa, #Hctx, HRD⟩
  iunfold v3rpc.amsIs at Hams
  icases Hams with ⟨%Hpn, #Hms, #Haaf⟩
  (try wp_auto)
  wp_apply (hP aa s E ctx cd) $$ [$HRD] as %err ⟨HRD, #Hout⟩
  · iframe #
  (try wp_auto)
  iapply HΦ
  iframe HRD
  iexact Hout

end proof

end EtcdGrove
end Perennial
