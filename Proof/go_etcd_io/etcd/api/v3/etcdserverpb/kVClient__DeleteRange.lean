/-
Proof of `Spec/go_etcd_io/etcd/api/v3/etcdserverpb/kVClient__DeleteRange.lean`. Lean-first (no Rocq
counterpart).
-/
module

public import Spec.go_etcd_io.etcd.api.v3.etcdserverpb.kVClient__DeleteRange
public import Spec.google_golang_org.grpc.StaticMethod
public import Spec.google_golang_org.grpc.ClientConn__Invoke
public import Proof.go_etcd_io.etcd.client.v3.EtcdInvoke

@[expose] public section

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

theorem kVClient.DeleteRange.wp_proof
    (wp_StaticMethod : grpc.StaticMethod.spec (GF := GF) (hG := hG))
    (wp_Invoke : grpc.ClientConn.Invoke.spec (GF := GF) (hG := hG)) :
    kVClient.DeleteRange.spec (GF := GF) (hG := hG) := by
  intro kc conn addr Spec Q ctx cd inp req k e opts vs
  wp_start as ⟨#Hstub, #Hconn, #Hrpc, #Hpre, #Hctx, Hin, #Hk, #He, #Hopts, #Hok⟩
  wp_auto
  wp_apply wp_StaticMethod as %sm #Hsm
  wp_apply wp_slice_literal (V := GoInterface) [sm]
  isplitr
  · ipureintro; rfl
  iintro %sl_ptr ⟨Hsl, Hcap⟩
  wp_auto
  wp_apply wp_slice_append $$ [$Hsl $Hcap $Hopts] as %copts ⟨Hco, Hcocap, -⟩
  iunfold kvStubAt at Hstub
  wp_auto
  ipersist Hco
  ihave #Hs1 := callOptsOk_singleton sm $$ Hsm
  ihave #Hok2 := callOptsOk_app [sm] vs $$ [Hs1 Hok]
  · iframe #
  ihave Hsend : pbDeleteRangeRequest (GF := GF) |>.send inp (deleteReqOp req k e) $$ [Hin]
  · simp only [pbDeleteRangeRequest]
    iexists req, k, e
    iframe
    iframe #
    ipureintro; rfl
  ihave Hblank : pbDeleteRangeResponse (GF := GF) |>.blank «$r0_ptr» $$ [«$r0»]
  · simp only [pbDeleteRangeResponse]
    iexact «$r0»
  have hI := etcdConn_Invoke wp_Invoke conn addr go!"/etcdserverpb.KV/DeleteRange" pbDeleteRangeRequest pbDeleteRangeResponse Spec (deleteReqOp req k e) Q ctx cd inp «$r0_ptr» copts
    ([sm] ++ vs)
  rw [show (pbDeleteRangeRequest (GF := GF)).ty = etcdserverpb.DeleteRangeRequest.ty from rfl,
    show (pbDeleteRangeResponse (GF := GF)).ty = etcdserverpb.DeleteRangeResponse.ty from rfl] at hI
  ihave Hpre' := reqPre_box conn addr _ $$ Hpre
  wp_apply hI $$ [Hsend Hblank Hpre'] as %err ⟨Hin', Hres⟩
  · iframe #
    iframe
  icases Hin' with ⟨%req', %k', %e', Hin', -⟩
  icases Hres with (⟨%Herr, %m', Hm, Hq⟩ | ⟨%Herr, #Hse⟩)
  · subst Herr
    wp_auto
    iapply HΦ
    iframe
    unfold deleteCallOut
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
      unfold deleteCallOut
      iright
      iframe #
      ipureintro
      exact ⟨Hne, Hce, rfl⟩

end proof

end EtcdGrove
end Perennial
