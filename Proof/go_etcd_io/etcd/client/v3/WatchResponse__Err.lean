/-
Proof of `Spec/WatchResponse__Err.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.WatchResponse__Err
public import Spec.go_etcd_io.etcd.api.v3.v3rpc.rpctypes.Error
public import Spec.go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError__Error
public import Proof.go_etcd_io.etcd.api.v3.v3rpc.rpctypes.Error
public import Spec.google_golang_org.grpc.status.Error
public import Proof.go_etcd_io.etcd.client.v3.CtxErrLeaf
public import Perennial.Proof.github_com.mit_pdos.perennial.goose.model.strings

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.cache.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

-- Loads from the fractional response: the field-store `AccessStrict` instances (which need
-- `DFrac.own 1`) are found first and the search does not backtrack.
attribute [-instance] go_etcd_io.etcd.client.v3.WatchResponse.WatchResponse_access_store_Header
  go_etcd_io.etcd.client.v3.WatchResponse.WatchResponse_access_store_Events
  go_etcd_io.etcd.client.v3.WatchResponse.WatchResponse_access_store_CompactRevision
  go_etcd_io.etcd.client.v3.WatchResponse.WatchResponse_access_store_Canceled
  go_etcd_io.etcd.client.v3.WatchResponse.WatchResponse_access_store_Created
  go_etcd_io.etcd.client.v3.WatchResponse.WatchResponse_access_store_closeErr
  go_etcd_io.etcd.client.v3.WatchResponse.WatchResponse_access_store_CancelReason

/-- An `EtcdError` value's `Error` is `Error() string`, from `rpctypesEtcdErrorTy` (fmt soundness 2). -/
theorem rpctypesEtcdErrorTy_errorSig (hty : rpctypesEtcdErrorTy (GF := GF) (hG := hG)) (e : GoInterfaceOk)
    (h : ∃ x : go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError,
      GoInterface.ok e = interface.mkOk go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty #x) :
    methodSet e.ty !! go!"Error" = some EtcdGrove.noArgStringSig := by
  obtain ⟨x, hx⟩ := h
  cases e
  simp only [interface.mkOk, GoInterface.ok.injEq, GoInterfaceOk.mk.injEq] at hx
  rw [hx.1]; exact hty.2.2.2.2

theorem statusErrOk_nil' : ⊢ statusErrOk (GF := GF) GoInterface.nil := by
  unfold statusErrOk
  iintro !> %e %he
  cases he

theorem WatchResponse.Err.wp_proof
    (wp_rpctypes_Error : rpctypes.Error.spec (GF := GF) (hG := hG))
    (wp_status_Error : status.Error.spec (GF := GF) (hG := hG))
    (wp_EErr : rpctypes.EtcdError.Error.spec (GF := GF) (hG := hG)) :
    WatchResponse.Err.spec (GF := GF) (hG := hG) := by
  intro wr resp dq
  wp_start as ⟨Hwr, #Hcse⟩
  ihave #Hrpc : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.v3rpc.rpctypes $$ []
  · iPkgInit
  ihave Hri : (rpctypesInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hrpc
  icases Hri with ⟨⟨%eFR, #HeFR, -, %FFR⟩, ⟨%eCP, #HeCP, #HeCPs, -, %FCP⟩, #HFR, -, %Hty, -⟩
  ihave #HeFRs := HFR $$ HeFR
  wp_auto
  cases hce : resp.closeErr' with
  | ok i =>
    wp_auto
    rw [hce]
    ihave ⟨%mR, #HmR⟩ := go_etcd_io.etcd.cache.v3.statusErrOk_descIs _ $$ Hcse
    wp_apply wp_rpctypes_Error (GoInterface.ok i) mR $$ [$Hcse $HmR] as %err' ⟨%Hne, #Hw, %Hce, -, #Hcell, %Hptr, -⟩
    · ipureintro; simp
    iapply HΦ
    iframe
    isplitl []
    · ipureintro; simp [Hne]
    isplitl []
    · imodintro; iintro -
      iapply errStrOk_of_statusErrOk; iexact Hw
    isplitl []
    · iexact Hw
    isplitl []
    · ipureintro; intro _ hc; exact Hce (hc (by simp))
    isplitl []
    · iexact Hcell
    ipureintro
    first
      | exact Hptr
      | (intro h; rw [hce] at h; exact Hptr h)
  | nil =>
    wp_auto
    wp_if_destruct
    · -- compacted
      iapply HΦ
      iframe
      isplitl []
      · ipureintro; simp_all
      isplitl []
      · imodintro; iintro -; iapply errStrOk_ok _ ⟨FCP.1, rpctypesEtcdErrorTy_errorSig Hty _ FCP.2⟩; iexact HeCPs
      obtain ⟨x, hx⟩ := FCP.2
      rw [hx]
      isplitl []
      · iapply rpctypes_etcdError_statusErrOk wp_EErr Hty
      isplitl []
      · ipureintro; intro hAs _
        exact rpctypes_etcdError_clientErr Hty GoInterface.nil ⟨hAs, fun _ h => by cases h⟩ x
      isplitl []
      · iintro !> -
        iapply errCellOk_of_ty
        unfold go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty; simp
      ipureintro; intro _
      exact errPtrOk_of_ty _ (by unfold go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty; simp)
    cases hca : resp.Canceled'
    · wp_auto
      iapply HΦ
      iframe
      isplitl []
      · ipureintro; simp_all
      isplitl []
      · imodintro; iintro -; iapply errStrOk_nil
      isplitl []
      · iapply statusErrOk_nil'
      isplitl []
      · ipureintro; intro hAs _
        exact ⟨hAs, fun _ h => by cases h⟩
      isplitl []
      · iintro !> -
        iapply errCellOk_nil
      ipureintro; intro _; exact errPtrOk_nil
    · wp_auto
      wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len as %-
      wp_if_destruct
      · -- `rpctypes.ErrFutureRev`
        iapply HΦ
        iframe
        isplitl []
        · ipureintro; simp
        isplitl []
        · imodintro; iintro -; iapply errStrOk_ok _ ⟨FFR.1, rpctypesEtcdErrorTy_errorSig Hty _ FFR.2⟩; iexact HeFRs
        obtain ⟨x, hx⟩ := FFR.2
        rw [hx]
        isplitl []
        · iapply rpctypes_etcdError_statusErrOk wp_EErr Hty
        isplitl []
        · ipureintro; intro hAs _
          exact rpctypes_etcdError_clientErr Hty GoInterface.nil ⟨hAs, fun _ h => by cases h⟩ x
        isplitl []
        · iintro !> -
          iapply errCellOk_of_ty
          unfold go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty; simp
        ipureintro; intro _
        exact errPtrOk_of_ty _ (by unfold go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty; simp)
      · -- a cancel reason: `rpctypes.Error(status.Error(codes.FailedPrecondition, reason))`
        wp_apply wp_status_Error as %e1 ⟨%He1, #He1s, -, %He1ty, -⟩
        · ipureintro
          simp only [google_golang_org.grpc.codes.OK]
          exact fun h => absurd (go.intoVal_inj h) (by decide)
        ihave ⟨%mR, #HmR⟩ := go_etcd_io.etcd.cache.v3.statusErrOk_descIs _ $$ He1s
        wp_apply wp_rpctypes_Error e1 mR $$ [] as %e2 ⟨%He2, #Hw, %Hce, -, #Hcell, %Hptr, -⟩
        · iframe #; ipureintro; exact He1
        obtain ⟨e1o, rfl⟩ : ∃ e1o, e1 = GoInterface.ok e1o := by
          cases e1 with
          | nil => exact absurd rfl He1
          | ok e => exact ⟨e, rfl⟩
        iunfold statusErrOk at He1s
        ihave ⟨-, %Hl1, -, -⟩ := He1s $$ %e1o %rfl
        iapply HΦ
        iframe
        isplitl []
        · ipureintro; simp [He2]
        isplitl []
        · imodintro; iintro -; iapply errStrOk_of_statusErrOk; iexact Hw
        isplitl []
        · iexact Hw
        isplitl []
        · ipureintro; intro hAs _
          exact Hce (clientErr_statusError e1o Hl1 (He1ty e1o rfl) hAs)
        isplitl []
        · iintro !> -
          iapply Hcell
          iapply errCellOk_of_ty
          rw [He1ty e1o rfl]
          unfold google_golang_org.grpc.internal.status.Error.ty _root_.Perennial.errors.errorString.ty
          simp
        ipureintro; intro _
        apply Hptr
        apply errPtrOk_of_ty
        rw [He1ty e1o rfl]
        unfold google_golang_org.grpc.internal.status.Error.ty _root_.Perennial.errors.errorString.ty
        simp

end proof

end EtcdGrove
end Perennial
