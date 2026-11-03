/-
Proof of `Spec/go_etcd_io/etcd/api/v3/etcdserverpb/authClient__Authenticate.lean` (the auth plan's
C1). Lean-first (no Rocq
counterpart).
-/
module

public import Spec.go_etcd_io.etcd.api.v3.etcdserverpb.authClient__Authenticate
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

theorem etcdserverpb.authClient.Authenticate.wp_proof
    (wp_StaticMethod : grpc.StaticMethod.spec (GF := GF) (hG := hG))
    (wp_Invoke : grpc.ClientConn.Invoke.spec (GF := GF) (hG := hG)) :
    etcdserverpb.authClient.Authenticate.spec (GF := GF) (hG := hG) := by
  intro ac conn addr Spec Q ctx cd inp m opts vs
  wp_start as ⟨#Hstub, #Hconn, #Hrpc, #Hpre, #Hctx, Hsend, #Hopts, #Hok, %Hsz⟩
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
  ihave Hblank : pbAuthenticateResponse (GF := GF) |>.blank «$r0_ptr» $$ [«$r0»]
  · simp only [pbAuthenticateResponse]
    iexact «$r0»
  have hI := etcdConn_Invoke wp_Invoke conn addr go!"/etcdserverpb.Auth/Authenticate" pbAuthenticateRequest pbAuthenticateResponse Spec m Q ctx cd inp «$r0_ptr» copts
    ([sm] ++ vs)
  rw [show (pbAuthenticateRequest (GF := GF)).ty = etcdserverpb.AuthenticateRequest.ty from rfl,
    show (pbAuthenticateResponse (GF := GF)).ty = etcdserverpb.AuthenticateResponse.ty from rfl] at hI
  ihave Hpre' : reqPre (GF := GF) conn go!"/etcdserverpb.Auth/Authenticate" addr ([sm] ++ vs) (Spec m Q) $$ []
  · iapply reqPre_box; iexact Hpre
  iunfold authnMethod at Hrpc
  wp_apply hI $$ [Hsend Hblank Hpre'] as %err ⟨Hin', Hres⟩
  · iframe #
    iframe
    try (ipureintro; first | exact Hsz.2 | exact Hsz | exact (by decide : wireSlack < grpcMsgMax))
  icases Hres with (⟨%Herr, %t, Hrecv, Hq⟩ | ⟨%Herr, #Hse⟩)
  · subst Herr
    wp_auto
    iapply HΦ
    isplitl [Hin']
    · simp only [pbAuthenticateRequest]; iexact Hin'
    unfold authnCallOut
    ileft
    isplitr
    · ipureintro; rfl
    iexists t
    iframe Hq
    simp only [pbAuthenticateResponse]; iexact Hrecv
  · obtain ⟨Hne, Hce⟩ := Herr
    cases err with
    | nil => exact absurd rfl Hne
    | ok ei =>
      wp_auto
      iapply HΦ
      isplitl [Hin']
      · simp only [pbAuthenticateRequest]; iexact Hin'
      unfold authnCallOut
      iright
      iframe #
      ipureintro
      exact ⟨Hne, Hce, rfl⟩


end proof

end EtcdGrove
end Perennial
