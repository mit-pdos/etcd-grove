/-
Proof of the spec of the same name (the client lease's stage (c)). Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.quotaLeaseServer__LeaseGrant
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.quotaAlarmer__check

@[expose] public section

set_option linter.unusedSectionVars false
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

theorem v3rpc.quotaLeaseServer.LeaseGrant.wp_proof
    (wp_check : v3rpc.quotaAlarmer.check.spec (GF := GF) (hG := hG)) :
    v3rpc.quotaLeaseServer.LeaseGrant.spec (GF := GF) (hG := hG) := by
  intro Req Rep Spec q s ls E ρ S m Φ' ci cd r
  wp_start_folded as ⟨#Hq, #Hh, #Hsrv, #HNR, HS, Hlt, Hard, #Hctx, #Hrc, #Hr, HSpec⟩
  rw [method_unfold (t := go.GoType.PointerType v3rpc.quotaLeaseServer.ty) (m := go!"LeaseGrant")]
  wp_call
  iunfold v3rpc.quotaLeaseServerAt at Hq
  icases Hq with ⟨%Hqn, #Hkv, #Hqa⟩
  wp_auto
  wp_apply wp_check _ s E ρ ci cd r (go.GoType.PointerType etcdserverpb.LeaseGrantRequest.ty) (Or.inr (Or.inr rfl))
    $$ [Hlt Hard] as %err ⟨Hlt, Hard⟩
  · iframe; iframe #
  cases err with
  | ok ei =>
    wp_auto
    iapply HΦ
    iframe
    iintro %Hc
    cases Hc
  | nil =>
    wp_auto
    iunfold grpcHandlerOk at Hh
    wp_apply Hh $$ %m %Φ' %ci %cd %r [HS HSpec] as %resp %err' ⟨HS, Hres⟩
    · iframe; iframe #
    iapply HΦ
    iframe

end proof

end EtcdGrove
end Perennial
