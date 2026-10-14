/-
Proof of `Spec/go_etcd_io/etcd/api/v3/etcdserverpb/kVClient__Range.lean`. Lean-first (no Rocq
counterpart).
-/
module

public import Spec.go_etcd_io.etcd.api.v3.etcdserverpb.kVClient__Range
public import Spec.google_golang_org.grpc.StaticMethod
public import Spec.google_golang_org.grpc.ClientConn__Invoke

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

theorem kVClient.Range.wp_proof
    (wp_StaticMethod : grpc.StaticMethod.spec (GF := GF) (hG := hG))
    (wp_Invoke : grpc.ClientConn.Invoke.spec (GF := GF) (hG := hG)) :
    kVClient.Range.spec (GF := GF) (hG := hG) := by
  intro kc conn K ctx cd inp req k e opts vs Q
  wp_start as ⟨#Hstub, #Hconn, #Hctx, Hin, #Hk, #He, #Hopts, #Hok, #Hrun⟩
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
  wp_apply wp_Invoke.2 conn K ctx cd inp _ req k e copts ([sm] ++ vs) Q $$ [Hin «$r0»]
    as %err ⟨Hin', Hres⟩
  · iframe #
    iframe
  icases Hres with (⟨%Herr, Hm⟩ | %Herr)
  · subst Herr
    wp_auto
    iapply HΦ
    iframe
    unfold rangeCallOut
    ileft
    iframe
    ipureintro; rfl
  · obtain ⟨Hne, Hce⟩ := Herr
    cases err with
    | nil => exact absurd rfl Hne
    | ok ei =>
      wp_auto
      iapply HΦ
      iframe
      unfold rangeCallOut
      iright
      ipureintro
      exact ⟨Hne, Hce, rfl⟩

end proof

end EtcdGrove
end Perennial
