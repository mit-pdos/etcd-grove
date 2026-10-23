/-
Proof of `Spec/go_etcd_io/etcd/api/v3/etcdserverpb/leaseClient__LeaseRevoke.lean` (item 1, the client
lease). Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.api.v3.etcdserverpb.leaseClient__LeaseRevoke
public import Spec.google_golang_org.grpc.StaticMethod
public import Spec.google_golang_org.grpc.ClientConn__Invoke
public import Proof.go_etcd_io.etcd.client.v3.EtcdInvoke

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.api.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

theorem leaseClient.LeaseRevoke.wp_proof
    (wp_StaticMethod : grpc.StaticMethod.spec (GF := GF) (hG := hG))
    (wp_Invoke : grpc.ClientConn.Invoke.spec (GF := GF) (hG := hG)) :
    leaseClient.LeaseRevoke.spec (GF := GF) (hG := hG) := by
  intro lc conn addr Spec Q ctx cd inp req opts vs
  wp_start as ⟨#Hstub, #Hconn, #Hrpc, #Hpre, #Hctx, Hin, #Hopts, #Hok⟩
  wp_auto
  wp_apply wp_StaticMethod as %sm ⟨#Hsm, %Hsms⟩
  wp_apply wp_slice_literal (V := GoInterface) [sm]
  isplitr
  · ipureintro; rfl
  iintro %sl_ptr ⟨Hsl, Hcap⟩
  wp_auto
  wp_apply wp_slice_append $$ [$Hsl $Hcap $Hopts] as %copts ⟨Hco, Hcocap, -⟩
  iunfold leaseStubAt at Hstub
  wp_auto
  ipersist Hco
  ihave #Hs1 := callOptsOk_singleton sm $$ Hsm
  ihave #Hok2 := callOptsOk_app [sm] vs $$ [Hs1 Hok]
  · iframe #
  ihave Hsend : pbLeaseRevokeRequest (GF := GF) |>.send inp req.ID' $$ [Hin]
  · simp only [pbLeaseRevokeRequest]
    iexists req
    iframe
    ipureintro; rfl
  ihave Hblank : pbLeaseRevokeResponse (GF := GF) |>.blank «$r0_ptr» $$ [«$r0»]
  · simp only [pbLeaseRevokeResponse]
    iexact «$r0»
  have hI := etcdConn_Invoke wp_Invoke conn addr go!"/etcdserverpb.Lease/LeaseRevoke" pbLeaseRevokeRequest
    pbLeaseRevokeResponse Spec req.ID' Q ctx cd inp «$r0_ptr» copts ([sm] ++ vs)
  rw [show (pbLeaseRevokeRequest (GF := GF)).ty = etcdserverpb.LeaseRevokeRequest.ty from rfl,
    show (pbLeaseRevokeResponse (GF := GF)).ty = etcdserverpb.LeaseRevokeResponse.ty from rfl] at hI
  ihave Hpre' := reqPre_box conn _ addr ([sm] ++ vs) _ $$ Hpre
  wp_apply hI $$ [Hsend Hblank Hpre'] as %err ⟨Hin', Hres⟩
  · iframe #
    iframe
  icases Hin' with ⟨%req', Hin', -⟩
  icases Hres with (⟨%Herr, %m', Hm, Hq⟩ | ⟨%Herr, #Hse, -⟩)
  · subst Herr
    wp_auto
    iapply HΦ
    iframe
    unfold leaseRevokeCallOut
    ileft
    isplitl []
    · ipureintro; rfl
    iexists m'
    iframe
  · obtain ⟨Hne, Hce⟩ := Herr
    cases err with
    | nil => exact absurd rfl Hne
    | ok ei =>
      wp_auto
      iapply HΦ
      iframe
      unfold leaseRevokeCallOut
      iright
      iframe #
      ipureintro
      exact ⟨Hne, Hce, rfl⟩

end proof

end EtcdGrove
end Perennial
