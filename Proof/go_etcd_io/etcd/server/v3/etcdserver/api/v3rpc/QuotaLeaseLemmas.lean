/-
**The Lease service's quota wrapper's methods as service methods** (the client lease's stage (c);
`InvLease.lean`): `quotaLeaseServer`'s `LeaseGrant` (from its spec,
`quotaLease_grantHandlerOk_of`) and `LeaseRevoke` (the embedded service's, promoted: a method-set
wrapper, `quotaLease_revokeHandlerOk`) meet a spec the embedded service's meet
(`grpcHandlerOk`); as `QuotaLemmas.lean`'s of the KV service. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.quotaLeaseServer__LeaseGrant

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver.api
  go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.etcd.api.v3

section lemmas
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

/-- **`quotaLeaseServer.LeaseGrant` meets the embedded service's spec**, with the reader slot of
`leadTimeMu` and the auth store's reader resource `E.RD` the alarm needs (from its spec). -/
theorem v3rpc.quotaLease_grantHandlerOk_of
    (wp_Grant : v3rpc.quotaLeaseServer.LeaseGrant.spec (GF := GF) (hG := hG))
    {Req Rep : ProtoMsg GF} (Spec : GrpcSpec Req Rep) (q s : Loc) (ls : GoInterfaceOk)
    (E : apply.AEnv GF) (ρ : ReqNames) (S : IProp GF) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗
        isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
        v3rpc.quotaLeaseServerAt q ls s ∗
        grpcHandlerOk #(methods ls.ty go!"LeaseGrant" ls.v) S Spec ∗
        isServerReq s E ρ ∗ □ (|==> idCred ρ.ids 1) ⊢
      grpcHandlerOk (q @!! go.GoType.PointerType v3rpc.quotaLeaseServer.ty @!! go!"LeaseGrant")
        iprop(S ∗ srvLeadTimeReader s ∗ E.RD) Spec := by
  iintro ⟨#Hp1, #Hp2, #Hq, #Hh, #Hsrv, #HNR⟩
  unfold grpcHandlerOk
  iintro %m %Φ %ci %cd %r !> %Ψ ⟨⟨HS, Hlt, Hard⟩, #Hctx, #Hrc, #Hr, HSpec⟩ HΨ
  iapply (wp_Grant Req Rep Spec q s ls E ρ S m Φ ci cd r) $$ [HS Hlt Hard HSpec]
  · iframe; iframe #
    unfold grpcHandlerOk
    iexact Hh
  inext
  iintro %resp %err ⟨HS, Hlt, Hard, Hres⟩
  iapply HΨ
  iframe

/-- **`quotaLeaseServer.LeaseRevoke`** (the embedded service's, promoted) meets what the embedded
service's meets. -/
theorem v3rpc.quotaLease_revokeHandlerOk {Req Rep : ProtoMsg GF} (Spec : GrpcSpec Req Rep)
    (q s : Loc) (ls : GoInterfaceOk) (S : IProp GF) :
    v3rpc.quotaLeaseServerAt (GF := GF) q ls s ∗
        grpcHandlerOk #(methods ls.ty go!"LeaseRevoke" ls.v) S Spec ⊢
      grpcHandlerOk (q @!! go.GoType.PointerType v3rpc.quotaLeaseServer.ty @!! go!"LeaseRevoke")
        S Spec := by
  iintro ⟨#Hq, #Hh⟩
  iunfold v3rpc.quotaLeaseServerAt at Hq
  icases Hq with ⟨%Hqn, #Hls, -⟩
  unfold grpcHandlerOk
  iintro %m %Φ %ci %cd %r !> %Ψ Hpre HΨ
  rw [method_unfold (t := go.GoType.PointerType v3rpc.quotaLeaseServer.ty) (m := go!"LeaseRevoke")]
  wp_pures
  wp_auto
  iapply Hh $$ %m %Φ %ci %cd %r Hpre
  inext
  iexact HΨ

end lemmas

end EtcdGrove
end Perennial
