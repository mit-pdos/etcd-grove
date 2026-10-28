/-
Proof of `Spec/go_etcd_io/etcd/server/v3/auth/authStore__IsAdminPermitted.lean`. Lean-first (no Rocq counterpart;
unit P2).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.auth.authStore__IsAdminPermitted
public import Proof.go_etcd_io.etcd.server.v3.auth.VerdictLemmas
public import Spec.go_etcd_io.etcd.server.v3.auth.authStore__IsAuthEnabled
public import Spec.go_etcd_io.etcd.server.v3.auth.hasRootRole
public import Spec.go_etcd_io.etcd.server.v3.auth.authStore__lockedReadTx

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.auth auth

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.auth.Assumptions]

theorem auth.authStore.IsAdminPermitted.wp_proof
    (h_IsAuthEnabled : auth.authStore.IsAuthEnabled.spec (GF := GF) (hG := hG))
    (h_lockedReadTx : auth.authStore.lockedReadTx.spec (GF := GF) (hG := hG))
    (h_hasRootRole : auth.hasRootRole.spec (GF := GF) (hG := hG)) :
    auth.authStore.IsAdminPermitted.spec (GF := GF) (hG := hG) := by
  intro st R M a ai dq
  wp_start as ⟨#Hinv, Hrd, Ha⟩
  iunfold authRd at Hrd
  icases Hrd with ⟨Hen, Hca, Hbr, HR⟩
  ihave Hai : (authInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  icases Hai with ⟨#HeUE, #HeUNF, #HePD, #HeOR, #HeIT, #Hs1, #Hs2, -⟩
  ihave #HeUE' := HeUE
  iunfold authErrVar at HeUE'
  icases HeUE' with ⟨%eUE, #HeUEa, -⟩
  ihave #HeUNF' := HeUNF
  iunfold authErrVar at HeUNF'
  icases HeUNF' with ⟨%eUNF, #HeUNFa, -⟩
  ihave #HePD' := HePD
  iunfold authErrVar at HePD'
  icases HePD' with ⟨%ePD, #HePDa, -⟩
  ihave #Hinv' := Hinv
  iunfold authInv at Hinv'
  icases Hinv' with ⟨%Hst, -, -, -, -, -, -⟩
  wp_auto
  wp_apply wp_with_defer as %defer defer
  (try wp_auto)
  wp_apply (h_IsAuthEnabled st R M) $$ [$Hinv $Hen] as %en ⟨Hen, #Hev⟩
  cases en
  · wp_auto
    iapply HΦ
    iunfold authRd
    iframe
    isplitl []
    · iunfold authErrIs; ileft; ipureintro; rfl
    · iapply adminVerdict_of_disabled M ai $$ Hev
  wp_auto
  cases ai with
  | none =>
    iunfold authInfoAt at Ha
    icases Ha with %Han
    subst Han
    (try wp_auto)
    iapply HΦ
    iunfold authRd
    iframe
    isplitl []
    · iunfold authInfoAt; ipureintro; rfl
    isplitl []
    · iunfold authErrIs
      iright
      iexists ErrUserEmpty, eUE
      iframe HeUEa
      ipureintro; simp
    · iapply (adminVerdict_noPrincipal M none (GoInterface.ok eUE) (fun h => by cases h)
        (fun _ h => by cases h)) $$ Hev
  | some info =>
    iunfold authInfoAt at Ha
    ihave %Hann := typedPointsto_not_null $$ Ha
    simp only [show decide (a = null) = false from decide_eq_false Hann]
    iStructNamed Ha
    wp_auto
    wp_if_destruct
    · (try wp_auto)
      ihave Ha : a ↦{dq} info $$ [Username Revision]
      · iapply typedPointsto_combine a info dq Hann
        simp only [TypedPointsto.typedPointstoDef]
        iframe
      iapply HΦ
      iunfold authRd
      iframe
      isplitl [Ha]
      · iunfold authInfoAt; iexact Ha
      isplitl []
      · iunfold authErrIs
        iright
        iexists ErrUserEmpty, eUE
        iframe HeUEa
        ipureintro; simp
      · iapply (adminVerdict_noPrincipal M (some info) (GoInterface.ok eUE) (fun h => by cases h)
          (fun i h => by cases h; exact Hif)) $$ Hev
    have hname : info.Username' ≠ [] := Hif
    wp_apply (h_lockedReadTx st R M) $$ [$Hinv $Hbr $HR] as %tx ⟨Hbr, Htx⟩
    iunfold authReadTxLocked at Htx
    icases Htx with ⟨%ti, %Hti, Htx⟩
    subst Hti
    icases Htx with ⟨%sta, %Hs, Htok, #Hsnap, #Hreads⟩
    iunfold authTxReads at Hreads
    icases Hreads with ⟨#Hrds, #HRU⟩
    iunfold authReaderOk at Hrds
    icases Hrds with ⟨#HUG, -, -, -, -⟩
    wp_auto
    wp_bind (App (Val #(methods ti.ty go!"UnsafeGetUser" ti.v)) (Val #info.Username'))
    iapply HUG $$ Htok
    inext
    iintro %u ⟨Htok, Hu⟩
    ihave Ha : a ↦{dq} info $$ [Username Revision]
    · iapply typedPointsto_combine a info dq Hann
      simp only [TypedPointsto.typedPointstoDef]
      iframe
    wp_auto
    wp_if_destruct
    · ihave %Hnone := userOut_null sta info.Username' $$ Hu
      (try wp_auto)
      wp_bind (App (Val #(methods ti.ty go!"RUnlock" ti.v)) (Val #()))
      iapply HRU $$ Htok
      inext
      iintro HR
      (try wp_auto)
      iapply HΦ
      iunfold authRd
      iframe
      isplitl [Ha]
      · iunfold authInfoAt; iexact Ha
      isplitl []
      · iunfold authErrIs
        iright
        iexists ErrUserNotFound, eUNF
        iframe HeUNFa
        ipureintro; simp
      · iapply (adminVerdict_noUser M info (GoInterface.ok eUNF) sta (fun h => by cases h)
          Hnone) $$ Hev Hsnap
    ihave Hu' := userOut_some u sta info.Username' Hif $$ Hu
    icases Hu' with ⟨%roles, %ur, %Hur, Hu⟩
    wp_apply h_hasRootRole $$ [$Hu] as %root ⟨Hu, %Hroot⟩
    · ipureintro; rw [Hur.2.1]; exact Hur.2.2
    cases root
    · have hn : ¬ isRoot roles := by rw [← Hur.2.1]; exact of_decide_eq_false Hroot.symm
      (try wp_auto)
      wp_bind (App (Val #(methods ti.ty go!"RUnlock" ti.v)) (Val #()))
      iapply HRU $$ Htok
      inext
      iintro HR
      (try wp_auto)
      iapply HΦ
      iunfold authRd
      iframe
      isplitl [Ha]
      · iunfold authInfoAt; iexact Ha
      isplitl []
      · iunfold authErrIs
        iright
        iexists ErrPermissionDenied, ePD
        iframe HePDa
        ipureintro; simp
      · iapply (adminVerdict_notRoot M info (GoInterface.ok ePD) sta roles (fun h => by cases h)
          Hur.1 hn) $$ Hev Hsnap
    · have hroot : isRoot roles := by rw [← Hur.2.1]; exact of_decide_eq_true Hroot.symm
      (try wp_auto)
      wp_bind (App (Val #(methods ti.ty go!"RUnlock" ti.v)) (Val #()))
      iapply HRU $$ Htok
      inext
      iintro HR
      (try wp_auto)
      iapply HΦ
      iunfold authRd
      iframe
      isplitl [Ha]
      · iunfold authInfoAt; iexact Ha
      isplitl []
      · iunfold authErrIs; ileft; ipureintro; rfl
      · iapply (adminVerdict_root M info sta roles hname Hur.1 hroot) $$ Hsnap

end proof

end EtcdGrove
end Perennial
