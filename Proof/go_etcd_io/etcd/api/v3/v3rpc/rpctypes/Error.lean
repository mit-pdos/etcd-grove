/-
Proof of `Spec/go_etcd_io/etcd/api/v3/v3rpc/rpctypes/Error.lean` (unit P3a, 2026-10-14; it was an
axiom). Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.api.v3.v3rpc.rpctypes.Error
public import Spec.go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrorDesc
public import Spec.go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError__Error
public import Spec.google_golang_org.grpc.status.FromError

@[expose] public section

noncomputable section
set_option linter.unusedSectionVars false

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.cache.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.api.v3.v3rpc.rpctypes.Assumptions]

/-- `EtcdError` is not an interface type (`errors.AsTypeTyped` of an `EtcdError` value). -/
theorem rpctypes_etcdError_asTypeTyped (x : go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError) :
    errors.AsTypeTyped go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError
      go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty
      ⟨go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty, #x⟩ := by
  unfold errors.AsTypeTyped
  have hu : underlying go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty =
      go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.underlying := go.is_underlying
  rw [hu]
  simp only [go.isInterfaceType]
  exact fun _ => ⟨x, rfl⟩

/-- **An `EtcdError` value is an error grpc's `status` accepts** (`statusErrOk`), given the
package's facts about its method set (`rpctypesEtcdErrorTy`). -/
theorem rpctypes_etcdError_statusErrOk
    (wp_EErr : rpctypes.EtcdError.Error.spec (GF := GF) (hG := hG))
    (hty : rpctypesEtcdErrorTy (GF := GF) (hG := hG))
    (x : go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError) :
    ⊢ statusErrOk (GF := GF)
      (interface.mkOk go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty #x) := by
  unfold statusErrOk
  iintro !> %e %he
  cases he
  isplitr
  · unfold errorStringSpec
    iintro !> %Φ HΦ
    wp_apply wp_EErr x
    iapply HΦ
  isplitr
  · ipureintro; exact hty.1 #x
  · unfold grpcErrMethodsOk
    isplitl
    · iintro %h
      simp [hty.2.1] at h
    · iintro %h
      simp [hty.2.2] at h

/-- An `EtcdError` value is a client error, if any client error exists (`clientErr`'s first
conjunct, `errors.AsTarget` of `EtcdError`, is about the type alone). -/
theorem rpctypes_etcdError_clientErr (hty : rpctypesEtcdErrorTy (GF := GF) (hG := hG))
    (err : GoInterface) (hc : clientErr err)
    (x : go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError) :
    clientErr (interface.mkOk go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty #x) := by
  refine ⟨hc.1, fun ii h => ?_⟩
  cases h
  exact ⟨hty.1 #x, rpctypes_etcdError_asTypeTyped x⟩

theorem rpctypes.Error.wp_proof
    (wp_ErrorDesc : rpctypes.ErrorDesc.spec (GF := GF) (hG := hG))
    (wp_FromError : EtcdGrove.status.FromError.spec (GF := GF) (hG := hG))
    (wp_EErr : rpctypes.EtcdError.Error.spec (GF := GF) (hG := hG)) :
    rpctypes.Error.spec (GF := GF) (hG := hG) := by
  intro err
  wp_start as ⟨%Hne, #Hok⟩
  ihave #Hrpc : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.v3rpc.rpctypes $$ []
  · iPkgInit
  ihave #Hst : isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.grpc.status $$ []
  · iPkgInit
  ihave Hri : (rpctypesInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hrpc
  icases Hri with ⟨-, -, -, ⟨%mref, %m, #Hmg, #Hm, #Hmv, -⟩, %Hty, -⟩
  obtain ⟨e, rfl⟩ : ∃ e, err = GoInterface.ok e := by
    cases err with
    | nil => exact absurd rfl Hne
    | ok e => exact ⟨e, rfl⟩
  wp_auto
  wp_apply wp_ErrorDesc (GoInterface.ok e) $$ [$Hok] as %d -
  wp_apply wp_map_lookup2 $$ [$Hm] as -
  cases hk : m !! d with
  | none =>
    simp only [Option.getD_none, Option.isSome_none]
    wp_auto
    iapply HΦ
    iframe #
    ipureintro
    exact ⟨Hne, id⟩
  | some v =>
    simp only [Option.getD_some, Option.isSome_some]
    wp_auto
    ihave #Hv := Hmv $$ %d %v %hk
    wp_apply wp_FromError v $$ [$Hst $Hv] as %ev %ok ⟨%Hnil, #HCode, #HMsg, -⟩
    cases ok
    · obtain ⟨ve, rfl⟩ : ∃ ve, v = GoInterface.ok ve := by
        cases v with
        | nil => exact absurd (Hnil rfl) (by simp)
        | ok ve => exact ⟨ve, rfl⟩
      wp_auto
      iunfold statusErrOk at Hv
      ihave ⟨#HE, -⟩ := Hv $$ %ve %rfl
      iunfold errorStringSpec at HE
      wp_apply HE as %str
      wp_apply HCode
      iapply HΦ
      isplitr
      · ipureintro; simp
      isplitr
      · iapply rpctypes_etcdError_statusErrOk wp_EErr Hty
      ipureintro
      exact fun hc => rpctypes_etcdError_clientErr Hty _ hc _
    · wp_auto
      wp_apply HMsg
      wp_apply HCode
      iapply HΦ
      isplitr
      · ipureintro; simp
      isplitr
      · iapply rpctypes_etcdError_statusErrOk wp_EErr Hty
      ipureintro
      exact fun hc => rpctypes_etcdError_clientErr Hty _ hc _

end proof

end EtcdGrove
end Perennial
