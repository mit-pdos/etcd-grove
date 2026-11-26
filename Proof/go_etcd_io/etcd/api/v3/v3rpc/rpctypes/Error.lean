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
variable [GooseExts] [GooseSemantics] [GooseInterp]
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
  · iexists x.desc'
    unfold errorMsgIs
    iintro !> %Φ HΦ
    wp_apply wp_EErr x
    iexact HΦ
  isplitr
  · ipureintro; exact hty.1 #x
  isplitr
  · unfold grpcErrMethodsOk
    isplitl
    · iintro %h
      simp [hty.2.1] at h
    · iintro %h
      simp [hty.2.2.1] at h
  · ipureintro; exact ⟨hty.2.2.2, stTypedErr_etcdError x⟩

/-- An `EtcdError` value is a client error, if any client error exists (`clientErr`'s first
conjunct, `errors.AsTarget` of `EtcdError`, is about the type alone). -/
theorem rpctypes_etcdError_clientErr (hty : rpctypesEtcdErrorTy (GF := GF) (hG := hG))
    (err : GoInterface) (hc : clientErr err)
    (x : go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError) :
    clientErr (interface.mkOk go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty #x) := by
  refine ⟨hc.1, fun ii h => ?_⟩
  cases h
  exact ⟨hty.1 #x, rpctypes_etcdError_asTypeTyped x, by simp [clientErrTys]⟩

/-- **`Error` over the map `errStringToError` itself** (prove-rpcmap, 2026-11-20): `Error.spec` with
the map's facts (`rpctypesInit`'s) and `ErrorDesc`'s triple under a persistent `P` that gives grpc's
`status` in place of `rpctypes`' `isPkgInit`, and one more conjunct: if `err`'s description is a key of
the map, the result is an `EtcdError` value of that description. For `rpctypes`' initializer, whose
client-side errors `Err* = Error(ErrGRPC*)` call it before the package's `isPkgInit` holds
(`InitLinked.lean`); `Error.wp_proof` is its instance at `rpctypes`' `isPkgInit`. (errdesc stage 2b,
2026-11-21) Over the description `m` the caller fixes (`descIs err m`), the map's values each with its
key as description. -/
theorem rpctypes.Error.wp_gen (P : IProp GF) [Persistent P]
    (hP : P ⊢ isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.grpc.status)
    (wp_ED : ∀ (err : GoError) (m : GoString),
      {{ P ∗ statusErrOk err ∗ descIs err m }}
        (App (Val (@! go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrorDesc)) (Val #err))
      {{ RET #m; True }})
    (wp_FromError : EtcdGrove.status.FromError.spec (GF := GF) (hG := hG))
    (wp_EErr : rpctypes.EtcdError.Error.spec (GF := GF) (hG := hG))
    (mref : Loc) (M : GMap GoString GoInterface)
    (Hty : rpctypesEtcdErrorTy (GF := GF) (hG := hG)) :
    ∀ (err : GoError) (m : GoString),
    {{ P ∗ globalAddr go_etcd_io.etcd.api.v3.v3rpc.rpctypes.errStringToError ↦□ mref ∗
        mref ↦$□ M ∗ (□ ∀ (k : GoString) (v : GoInterface), ⌜M !! k = some v⌝ → statusErrOk v) ∗
        (□ ∀ (k : GoString) (v : GoInterface), ⌜M !! k = some v⌝ → descIs v k) ∗
        ⌜err ≠ interface.nil⌝ ∗ statusErrOk err ∗ descIs err m }}
      (App (Val (@! go_etcd_io.etcd.api.v3.v3rpc.rpctypes.Error)) (Val #err))
    {{ (err' : GoError), RET #err'; ⌜err' ≠ interface.nil⌝ ∗ statusErrOk err' ∗
        ⌜clientErr err → clientErr err'⌝ ∗
        descIs err' m ∗
        □ (errCellOk err -∗ errCellOk err') ∗
        ⌜errPtrOk err → errPtrOk err'⌝ ∗
        ⌜(err' = err ∨ ∃ x : go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError,
            err' = interface.mkOk go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty #x ∧ x.desc' = m) ∧
          ((M !! m).isSome →
          ∃ x : go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError,
            err' = interface.mkOk go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty #x ∧ x.desc' = m)⌝ }} := by
  intro err m
  wp_start as ⟨#HP, #Hmg, #HM, #Hmv, #Hmd, %Hne, #Hok, #Hm⟩
  ihave #Hst := hP $$ HP
  obtain ⟨e, rfl⟩ : ∃ e, err = GoInterface.ok e := by
    cases err with
    | nil => exact absurd rfl Hne
    | ok e => exact ⟨e, rfl⟩
  wp_auto
  wp_apply wp_ED (GoInterface.ok e) m $$ [$HP $Hok $Hm]
  wp_apply wp_map_lookup2 $$ [$HM] as -
  cases hk : M !! m with
  | none =>
    simp only [Option.getD_none, Option.isSome_none]
    wp_auto
    iapply HΦ
    iframe #
    isplitr
    · ipureintro; exact Hne
    isplitr
    · ipureintro; exact id
    isplitl
    · iintro !> #H; iexact H
    isplitl
    · ipureintro; exact id
    ipureintro
    exact ⟨Or.inl rfl, fun h => by simp at h⟩
  | some v =>
    simp only [Option.getD_some, Option.isSome_some]
    wp_auto
    ihave #Hv := Hmv $$ %m %v %hk
    ihave #Hvd := Hmd $$ %m %v %hk
    ihave ⟨%cFE, #HcFE⟩ := go_etcd_io.etcd.cache.v3.statusErrOk_code _ $$ Hv
    wp_apply wp_FromError v m cFE $$ [$Hst $Hv $Hvd $HcFE] as %ev %ok ⟨%Hnil, #HCode, #HMsg, #HErr, -⟩
    cases ok
    · obtain ⟨ve, rfl⟩ : ∃ ve, v = GoInterface.ok ve := by
        cases v with
        | nil => exact absurd (Hnil rfl) (by simp)
        | ok ve => exact ⟨ve, rfl⟩
      wp_auto
      -- (D29) not a status error: its `Error()` returns its description
      have hpe : false = false ∧ GoInterface.ok ve = GoInterface.ok ve := ⟨rfl, rfl⟩
      ihave #HE := HErr $$ %ve %hpe
      wp_apply HE
      wp_apply HCode
      iapply HΦ
      isplitr
      · ipureintro; simp
      isplitr
      · iapply rpctypes_etcdError_statusErrOk wp_EErr Hty
      isplitr
      · ipureintro; exact fun hc => rpctypes_etcdError_clientErr Hty _ hc _
      isplitr
      · iapply (descIs_etcdError_of _ _ rfl)
      isplitl
      · iintro !> -
        iapply go_etcd_io.etcd.cache.v3.errCellOk_of_ty
        simp [go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty]
      isplitl
      · ipureintro; intro _
        exact errPtrOk_of_ty _ (by simp [go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty])
      ipureintro
      exact ⟨Or.inr ⟨_, rfl, rfl⟩, fun _ => ⟨_, rfl, rfl⟩⟩
    · wp_auto
      wp_apply HMsg
      wp_apply HCode
      iapply HΦ
      isplitr
      · ipureintro; simp
      isplitr
      · iapply rpctypes_etcdError_statusErrOk wp_EErr Hty
      isplitr
      · ipureintro; exact fun hc => rpctypes_etcdError_clientErr Hty _ hc _
      isplitr
      · iapply (descIs_etcdError_of _ _ rfl)
      isplitl
      · iintro !> -
        iapply go_etcd_io.etcd.cache.v3.errCellOk_of_ty
        simp [go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty]
      isplitl
      · ipureintro; intro _
        exact errPtrOk_of_ty _ (by simp [go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty])
      ipureintro
      exact ⟨Or.inr ⟨_, rfl, rfl⟩, fun _ => ⟨_, rfl, rfl⟩⟩

theorem rpctypes.Error.wp_proof
    (wp_ErrorDesc : rpctypes.ErrorDesc.spec (GF := GF) (hG := hG))
    (wp_FromError : EtcdGrove.status.FromError.spec (GF := GF) (hG := hG))
    (wp_EErr : rpctypes.EtcdError.Error.spec (GF := GF) (hG := hG)) :
    rpctypes.Error.spec (GF := GF) (hG := hG) := by
  intro err m
  wp_start_folded as ⟨%Hne, #Hok, #Hm⟩
  ihave #Hrpc : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.v3rpc.rpctypes $$ []
  · iPkgInit
  ihave Hri : (rpctypesInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hrpc
  icases Hri with ⟨-, -, -, ⟨%mref, %M, #Hmg, #HM, #Hmv, #Hmd⟩, %Hty, -⟩
  have hP : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.v3rpc.rpctypes ⊢
      isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.grpc.status := by
    iintro #Hrpc
    iPkgInit
  wp_apply (rpctypes.Error.wp_gen _ hP wp_ErrorDesc wp_FromError wp_EErr mref M Hty err m)
    $$ [$Hrpc $Hmg $HM $Hmv $Hmd $Hok $Hm] as %err' ⟨%H1, #H2, %H3, #H4, #H5, %H6, %H7⟩
  · ipureintro; exact Hne
  iapply HΦ
  iframe #
  ipureintro
  exact ⟨H1, H3, H6, H7.1⟩

/-- **`Err* = Error(ErrGRPC*)` in `rpctypes`' initializer** (prove-rpcmap, 2026-11-20): `Error` of an
error grpc's `status` accepts whose description `d` is a key of the map `errStringToError` (given by its
facts, before the package's `isPkgInit` holds; `ErrorDesc`'s triple over grpc's `status`,
`ErrorDesc.wp_init`) returns an `EtcdError` value with that description, whose `Error()` returns. -/
theorem rpctypes.Error.wp_initErr
    (wp_ED : ∀ (err : GoError) (m : GoString),
      {{ isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.grpc.status ∗ statusErrOk err ∗
          descIs err m }}
        (App (Val (@! go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrorDesc)) (Val #err))
      {{ RET #m; True }})
    (wp_FromError : EtcdGrove.status.FromError.spec (GF := GF) (hG := hG))
    (wp_EErr : rpctypes.EtcdError.Error.spec (GF := GF) (hG := hG))
    (Hty : rpctypesEtcdErrorTy (GF := GF) (hG := hG))
    {mref : Loc} {M : GMap GoString GoInterface} (e : GoInterfaceOk) (d : GoString) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.grpc.status ∗
        globalAddr go_etcd_io.etcd.api.v3.v3rpc.rpctypes.errStringToError ↦□ mref ∗
        mref ↦$□ M ∗ (□ ∀ (k : GoString) (v : GoInterface), ⌜M !! k = some v⌝ → statusErrOk v) ∗
        (□ ∀ (k : GoString) (v : GoInterface), ⌜M !! k = some v⌝ → descIs v k) ∗
        statusErrOk (GoInterface.ok e) ∗ descIs (GoInterface.ok e) d ∗ ⌜(M !! d).isSome⌝ }}
      (App (Val (@! go_etcd_io.etcd.api.v3.v3rpc.rpctypes.Error)) (Val #(GoInterface.ok e)))
    {{ (x : go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError),
        RET #(interface.mkOk go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty #x);
        ⌜x.desc' = d⌝ ∗
        errorStringSpec ⟨go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty, #x⟩ }} := by
  wp_start_folded as ⟨#Hmg, #HM, #Hmv, #Hmd, #Hok, #Hd, %hk⟩
  ihave #Hst : isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.grpc.status $$ []
  · iPkgInit
  wp_apply (rpctypes.Error.wp_gen _ (by iintro #H; iexact H) wp_ED wp_FromError wp_EErr mref M Hty
      (GoInterface.ok e) d) $$ [$Hst $Hmg $HM $Hmv $Hmd $Hok $Hd]
    as %err' ⟨-, #Hs', -, -, -, -, %Hx⟩
  · ipureintro; simp
  obtain ⟨x, rfl, hx⟩ := Hx.2 hk
  iapply HΦ
  isplitr
  · ipureintro; exact hx
  · ihave ⟨%m', #Hm'⟩ := go_etcd_io.etcd.cache.v3.statusErrOk_msg _ $$ Hs'
    iapply go_etcd_io.etcd.cache.v3.errorMsgIs_errorStringSpec
    iapply Hm'
    ipureintro; rfl

/-- **`Err* = Error(ErrGRPC*)` in `rpctypes`' initializer, any key** (prove-rpcmap, 2026-11-20): as
`wp_initErr`, for an error whose description need not be a key of the map
(`ErrTimeoutWaitAppliedIndex`): it returns. -/
theorem rpctypes.Error.wp_initAny
    (wp_ED : ∀ (err : GoError) (m : GoString),
      {{ isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.grpc.status ∗ statusErrOk err ∗
          descIs err m }}
        (App (Val (@! go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrorDesc)) (Val #err))
      {{ RET #m; True }})
    (wp_FromError : EtcdGrove.status.FromError.spec (GF := GF) (hG := hG))
    (wp_EErr : rpctypes.EtcdError.Error.spec (GF := GF) (hG := hG))
    (Hty : rpctypesEtcdErrorTy (GF := GF) (hG := hG))
    {mref : Loc} {M : GMap GoString GoInterface} (e : GoInterfaceOk) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.grpc.status ∗
        globalAddr go_etcd_io.etcd.api.v3.v3rpc.rpctypes.errStringToError ↦□ mref ∗
        mref ↦$□ M ∗ (□ ∀ (k : GoString) (v : GoInterface), ⌜M !! k = some v⌝ → statusErrOk v) ∗
        (□ ∀ (k : GoString) (v : GoInterface), ⌜M !! k = some v⌝ → descIs v k) ∗
        statusErrOk (GoInterface.ok e) }}
      (App (Val (@! go_etcd_io.etcd.api.v3.v3rpc.rpctypes.Error)) (Val #(GoInterface.ok e)))
    {{ (err' : GoError), RET #err'; True }} := by
  wp_start_folded as ⟨#Hmg, #HM, #Hmv, #Hmd, #Hok⟩
  ihave #Hst : isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.grpc.status $$ []
  · iPkgInit
  ihave ⟨%m, #Hm⟩ := go_etcd_io.etcd.cache.v3.statusErrOk_descIs _ $$ Hok
  wp_apply (rpctypes.Error.wp_gen _ (by iintro #H; iexact H) wp_ED wp_FromError wp_EErr mref M Hty
      (GoInterface.ok e) m) $$ [$Hst $Hmg $HM $Hmv $Hmd $Hok $Hm] as %err' -
  · ipureintro; simp
  iapply HΦ
  itrivial

end proof

end EtcdGrove
end Perennial
