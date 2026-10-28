/-
Proof of `Spec/go_etcd_io/etcd/client/v3/Client__refreshToken.lean` (unit P3a). Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.Client__refreshToken
public import Spec.go_etcd_io.etcd.client.v3.Client__getToken

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.api.v3
open go_etcd_io.etcd.cache.v3 (statusErrOk statusErrOk_nil backoffOk errorStringSpec)

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

theorem Client.refreshToken.wp_proof
    (wp_getToken : Client.getToken.spec (GF := GF) (hG := hG)) :
    Client.refreshToken.spec (GF := GF) (hG := hG) := by
  intro c conn eps ctx cd
  wp_start as ⟨#Hc, #Hr, #Hconn, Hctx, #Hce⟩
  ihave #Hc' := Hc
  iunfold retryClientOk at Hc'
  icases Hc' with ⟨%Hcn, #Hlg, %tok, %atb, #Htok, #Hatb, %Htokatb⟩
  wp_auto
  cases atb with
  | nil =>
    wp_auto
    iapply HΦ
    iapply clientErrOk_nil
  | ok a =>
    wp_auto
    wp_apply wp_getToken c conn eps ctx cd $$ [$Hc $Hr $Hconn $Hctx $Hce] as %err ⟨#Herr, -⟩
    iapply HΦ
    iexact Herr

end proof

end EtcdGrove
end Perennial
