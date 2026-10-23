/-
Proof of `Spec/go_etcd_io/etcd/server/v3/auth/authStore__isOpPermitted.lean`. Lean-first (no Rocq counterpart;
unit P2).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.auth.authStore__isOpPermitted
public import Spec.go_etcd_io.etcd.server.v3.auth.authStore__IsAuthEnabled
public import Spec.go_etcd_io.etcd.server.v3.auth.authStore__Revision
public import Spec.go_etcd_io.etcd.server.v3.auth.authStore__isRangeOpPermitted
public import Spec.go_etcd_io.etcd.server.v3.auth.hasRootRole
public import Spec.go_etcd_io.etcd.server.v3.auth.authStore__lockedReadTx
public import Spec.go_uber_org.zap.Uint64
public import Spec.go_uber_org.zap.ByteString
public import Spec.go_uber_org.zap.Error
public import Spec.go_uber_org.zap.Logger__Warn
public import Spec.go_uber_org.zap.String
public import Spec.go_uber_org.zap.Logger__Error

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.auth auth

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.auth.Assumptions]

theorem auth.authStore.isOpPermitted.wp_proof
    (h_IsAuthEnabled : auth.authStore.IsAuthEnabled.spec (GF := GF) (hG := hG))
    (h_Revision : auth.authStore.Revision.spec (GF := GF) (hG := hG))
    (h_Uint64 : zap.Uint64.spec (GF := GF) (hG := hG))
    (h_ByteString : zap.ByteString.spec (GF := GF) (hG := hG))
    (h_ZError : zap.Error.spec (GF := GF) (hG := hG))
    (h_Warn : zap.Logger.Warn.spec (GF := GF) (hG := hG))
    (h_String : zap.String.spec (GF := GF) (hG := hG))
    (h_Error : zap.Logger.Error.spec (GF := GF) (hG := hG))
    (h_hasRootRole : auth.hasRootRole.spec (GF := GF) (hG := hG))
    (h_lockedReadTx : auth.authStore.lockedReadTx.spec (GF := GF) (hG := hG))
    (h_isRangeOpPermitted : auth.authStore.isRangeOpPermitted.spec (GF := GF) (hG := hG)) :
    auth.authStore.isOpPermitted.spec (GF := GF) (hG := hG) := by
  intro st R M user rev key re k e dk de pt
  wp_start as ⟨#Hinv, Hrd, Hk, He, %Hpt, %Hlen⟩
  iunfold authRd at Hrd
  icases Hrd with ⟨Hen, Hca, Hbr, HR⟩
  ihave #Hzap : isPkgInit (PROP := IProp GF) pkg_id.go_uber_org.zap $$ []
  · iPkgInit
  ihave Hai : (authInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  icases Hai with ⟨#HeUE, #HeUNF, #HePD, #HeOR, #HeIT, -, -⟩
  ihave #HeUE' := HeUE
  iunfold authErrVar at HeUE'
  icases HeUE' with ⟨%eUE, #HeUEa, -⟩
  ihave #HePD' := HePD
  iunfold authErrVar at HePD'
  icases HePD' with ⟨%ePD, #HePDa, -⟩
  ihave #HeOR' := HeOR
  iunfold authErrVar at HeOR'
  icases HeOR' with ⟨%eOR, #HeORa, -⟩
  ihave #Hinv' := Hinv
  iunfold authInv at Hinv'
  icases Hinv' with ⟨%Hst, -, ⟨%lg, #Hlg, %Hlgnn⟩, -, -, -, -⟩
  wp_apply wp_with_defer as %defer defer
  (try wp_auto)
  wp_apply (h_IsAuthEnabled st R M) $$ [$Hinv $Hen] as %en Hen
  cases en
  · wp_auto
    iapply HΦ
    iunfold authRd
    iframe
    iunfold authErrIs; ileft; ipureintro; rfl
  wp_auto
  wp_if_destruct
  · iapply HΦ
    iunfold authRd
    iframe
    iunfold authErrIs
    iright
    iexists ErrUserEmpty, eUE
    iframe HeUEa
    ipureintro; simp
  wp_apply (h_Revision st R M) $$ [$Hinv] as %cur -
  (try wp_auto)
  wp_if_destruct
  · wp_apply h_Uint64 _ _ as %f1 -
    wp_apply h_Uint64 _ _ as %f2 -
    wp_apply h_ByteString _ _ as %f3 -
    (try wp_auto)
    wp_apply h_ZError _ as %f4 -
    (try wp_auto)
    wp_apply wp_slice_literal (V := go_uber_org.zap.zapcore.Field) [f1, f2, f3, f4]
    isplitr
    · ipureintro; rfl
    iintro %fsl ⟨-, -⟩
    (try wp_auto)
    wp_apply h_Warn
    · ipureintro; exact Hlgnn
    iapply HΦ
    iunfold authRd
    iframe
    iunfold authErrIs
    iright
    iexists ErrAuthOldRevision, eOR
    iframe HeORa
    ipureintro; simp
  wp_apply (h_lockedReadTx st R M) $$ [$Hinv $Hbr $HR] as %tx ⟨Hbr, Htx⟩
  iunfold authReadTxLocked at Htx
  icases Htx with ⟨%ti, %Hti, Htx⟩
  subst Hti
  icases Htx with ⟨%sta, %Hs, Htok, #Hsnap, #Hreads⟩
  iunfold authTxReads at Hreads
  icases Hreads with ⟨#HUG, -, -, -, #HRU⟩
  wp_auto
  wp_bind (App (Val #(methods ti.ty go!"UnsafeGetUser" ti.v)) (Val #user))
  iapply HUG $$ Htok
  inext
  iintro %u ⟨Htok, -⟩
  wp_auto
  wp_if_destruct
  · wp_apply h_String _ _ as %f -
    (try wp_auto)
    wp_apply wp_slice_literal (V := go_uber_org.zap.zapcore.Field) [f]
    isplitr
    · ipureintro; rfl
    iintro %fsl ⟨-, -⟩
    (try wp_auto)
    wp_apply h_Error
    · ipureintro; exact Hlgnn
    (try wp_auto)
    wp_bind (App (Val #(methods ti.ty go!"RUnlock" ti.v)) (Val #()))
    iapply HRU $$ Htok
    inext
    iintro HR
    (try wp_auto)
    iapply HΦ
    iunfold authRd
    iframe
    iunfold authErrIs
    iright
    iexists ErrPermissionDenied, ePD
    iframe HePDa
    ipureintro; simp
  wp_apply h_hasRootRole $$ [] as %root -
  · ipureintro; assumption
  cases root
  · (try wp_auto)
    wp_apply (h_isRangeOpPermitted st R M user key re k e dk de pt) $$ [$Hinv $Hca $Hk $He]
      as %okr ⟨Hca, Hk, He⟩
    · ipureintro; exact ⟨Hpt, Hlen⟩
    cases okr
    · (try wp_auto)
      wp_bind (App (Val #(methods ti.ty go!"RUnlock" ti.v)) (Val #()))
      iapply HRU $$ Htok
      inext
      iintro HR
      (try wp_auto)
      iapply HΦ
      iunfold authRd
      iframe
      iunfold authErrIs
      iright
      iexists ErrPermissionDenied, ePD
      iframe HePDa
      ipureintro; simp
    · (try wp_auto)
      wp_bind (App (Val #(methods ti.ty go!"RUnlock" ti.v)) (Val #()))
      iapply HRU $$ Htok
      inext
      iintro HR
      (try wp_auto)
      iapply HΦ
      iunfold authRd
      iframe
      iunfold authErrIs; ileft; ipureintro; rfl
  · (try wp_auto)
    wp_bind (App (Val #(methods ti.ty go!"RUnlock" ti.v)) (Val #()))
    iapply HRU $$ Htok
    inext
    iintro HR
    (try wp_auto)
    iapply HΦ
    iunfold authRd
    iframe
    iunfold authErrIs; ileft; ipureintro; rfl

end proof

end EtcdGrove
end Perennial
