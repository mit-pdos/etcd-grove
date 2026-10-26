/-
Proof of `Spec/go_etcd_io/etcd/api/v3/etcdserverpb/authClient__RoleAdd.lean`. Lean-first (no Rocq
counterpart).
-/
module

public import Spec.go_etcd_io.etcd.api.v3.etcdserverpb.authClient__RoleAdd
public import Spec.google_golang_org.grpc.StaticMethod
public import Spec.google_golang_org.grpc.ClientConn__Invoke
public import Proof.go_etcd_io.etcd.client.v3.EtcdInvoke

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.api.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

theorem etcdserverpb.authClient.RoleAdd.wp_proof
    (wp_StaticMethod : grpc.StaticMethod.spec (GF := GF) (hG := hG))
    (wp_Invoke : grpc.ClientConn.Invoke.spec (GF := GF) (hG := hG)) :
    etcdserverpb.authClient.RoleAdd.spec (GF := GF) (hG := hG) := by
  intro ac conn addr Spec Q ctx cd inp m opts vs
  wp_start as ⟨#Hstub, #Hconn, #Hrpc, #Hpre, #Hctx, Hsend, #Hopts, #Hok⟩
  wp_auto
  wp_apply wp_StaticMethod as %sm ⟨#Hsm, %Hsms⟩
  wp_apply wp_slice_literal (V := GoInterface) [sm]
  isplitr
  · ipureintro; rfl
  iintro %sl_ptr ⟨Hsl, Hcap⟩
  wp_auto
  wp_apply wp_slice_append $$ [$Hsl $Hcap $Hopts] as %copts ⟨Hco, Hcocap, -⟩
  iunfold authStubAt at Hstub
  wp_auto
  ipersist Hco
  ihave #Hs1 := callOptsOk_singleton sm $$ Hsm
  ihave #Hok2 := callOptsOk_app [sm] vs $$ [Hs1 Hok]
  · iframe #
  ihave Hblank : pbAuthRoleAddResponse (GF := GF) |>.blank «$r0_ptr» $$ [«$r0»]
  · simp only [pbAuthRoleAddResponse]
    iexact «$r0»
  have hI := etcdConn_Invoke wp_Invoke conn addr go!"/etcdserverpb.Auth/RoleAdd" pbAuthRoleAddRequest pbAuthRoleAddResponse Spec m Q ctx cd inp «$r0_ptr» copts
    ([sm] ++ vs)
  rw [show (pbAuthRoleAddRequest (GF := GF)).ty = etcdserverpb.AuthRoleAddRequest.ty from rfl,
    show (pbAuthRoleAddResponse (GF := GF)).ty = etcdserverpb.AuthRoleAddResponse.ty from rfl] at hI
  ihave Hpre' : reqPre (GF := GF) conn go!"/etcdserverpb.Auth/RoleAdd" addr ([sm] ++ vs) (Spec m Q) $$ []
  · iapply reqPre_box; iexact Hpre
  wp_apply hI $$ [Hsend Hblank Hpre'] as %err ⟨Hin', Hres⟩
  · iframe #
    iframe
  icases Hres with (⟨%Herr, %m', -, Hq⟩ | ⟨%Herr, #Hse⟩)
  · subst Herr
    wp_auto
    iapply HΦ
    isplitl [Hin']
    · simp only [pbAuthRoleAddRequest]; iexact Hin'
    unfold authCallOut
    ileft
    iframe
    ipureintro; rfl
  · obtain ⟨Hne, Hce⟩ := Herr
    cases err with
    | nil => exact absurd rfl Hne
    | ok ei =>
      wp_auto
      iapply HΦ
      isplitl [Hin']
      · simp only [pbAuthRoleAddRequest]; iexact Hin'
      unfold authCallOut
      iright
      iframe #
      ipureintro
      exact ⟨Hne, Hce, rfl⟩

end proof

end EtcdGrove
end Perennial
