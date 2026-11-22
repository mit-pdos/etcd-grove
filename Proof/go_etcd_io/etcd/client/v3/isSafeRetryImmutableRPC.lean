/-
Proof of `Spec/go_etcd_io/etcd/client/v3/isSafeRetryImmutableRPC.lean` (unit P3a). Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.isSafeRetryImmutableRPC
public import Spec.google_golang_org.grpc.status.FromError
public import Spec.go_etcd_io.etcd.api.v3.v3rpc.rpctypes.Error
public import Spec.go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError__Code
public import Perennial.Proof.errors

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

theorem isSafeRetryImmutableRPC.wp_proof
    (wp_rpctypes_Error : rpctypes.Error.spec (GF := GF) (hG := hG))
    (wp_ECode : rpctypes.EtcdError.Code.spec (GF := GF) (hG := hG))
    (wp_FromError : EtcdGrove.status.FromError.spec (GF := GF) (hG := hG)) :
    isSafeRetryImmutableRPC.spec (GF := GF) (hG := hG) := by
  intro err
  wp_start as ⟨%Herr, #Hse⟩
  obtain ⟨Hne, Hce⟩ := Herr
  ihave #Hst : isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.grpc.status $$ []
  · iPkgInit
  wp_auto
  ihave ⟨%mR, #HmR⟩ := go_etcd_io.etcd.cache.v3.statusErrOk_descIs _ $$ Hse
  wp_apply wp_rpctypes_Error err mR $$ [$Hse $HmR] as %e1' ⟨%Hne1, #Hse1, %Hce1, -⟩
  · ipureintro; exact Hne
  have Hc1 := Hce1 Hce
  obtain ⟨e1, rfl⟩ : ∃ e1, e1' = GoInterface.ok e1 := by
    cases e1' with
    | nil => exact absurd rfl Hne1
    | ok e => exact ⟨e, rfl⟩
  obtain ⟨-, Hce'⟩ := Hc1
  obtain ⟨Hleaf, Htyped, -⟩ := Hce' e1 rfl
  ihave #Htree := errors.isErrorTree_leaf (GF := GF) e1 Hleaf Htyped
  wp_apply errors.wp_AsType (T' := go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError)
      (T := go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty) (· = GoInterface.ok e1)
      (GoInterface.ok e1) $$ [$Htree] as %v' %b -
  · ipureintro; rfl
  cases b
  · wp_auto
    ihave ⟨%mF, #HmF⟩ := go_etcd_io.etcd.cache.v3.statusErrOk_descIs _ $$ Hse
    ihave ⟨%cFE, #HcFE⟩ := go_etcd_io.etcd.cache.v3.statusErrOk_code _ $$ Hse
    wp_apply wp_FromError err mF cFE $$ [$Hst $Hse $HmF $HcFE] as %ev %ok ⟨-, #HCode, -⟩
    cases ok
    · wp_auto
      iapply HΦ; itrivial
    · wp_auto
      wp_apply HCode
      iapply HΦ; itrivial
  · wp_auto
    wp_method_call
    wp_auto
    wp_apply wp_ECode v'
    wp_if_destruct
    · ihave ⟨%mF, #HmF⟩ := go_etcd_io.etcd.cache.v3.statusErrOk_descIs _ $$ Hse
      ihave ⟨%cFE, #HcFE⟩ := go_etcd_io.etcd.cache.v3.statusErrOk_code _ $$ Hse
      wp_apply wp_FromError err mF cFE $$ [$Hst $Hse $HmF $HcFE] as %ev %ok ⟨-, #HCode, -⟩
      cases ok
      · wp_auto
        iapply HΦ; itrivial
      · wp_auto
        wp_apply HCode
        iapply HΦ; itrivial
    · iapply HΦ; itrivial

end proof

end EtcdGrove
end Perennial
