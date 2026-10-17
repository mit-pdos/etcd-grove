/-
Proof of `Spec/go_etcd_io/etcd/server/v3/auth/authStore__IsAdminPermitted.lean`. Lean-first (no Rocq counterpart;
unit P2).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.auth.authStore__IsAdminPermitted
public import Spec.go_etcd_io.etcd.server.v3.auth.authStore__IsAuthEnabled
public import Spec.go_etcd_io.etcd.server.v3.auth.hasRootRole

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

theorem auth.authStore.IsAdminPermitted.wp_proof
    (h_IsAuthEnabled : auth.authStore.IsAuthEnabled.spec (GF := GF) (hG := hG))
    (h_hasRootRole : auth.hasRootRole.spec (GF := GF) (hG := hG)) :
    auth.authStore.IsAdminPermitted.spec (GF := GF) (hG := hG) := by
  intro st R a info dq
  wp_start as ⟨#Hinv, Hrd, Ha⟩
  iunfold authRd at Hrd
  icases Hrd with ⟨Hen, Hca, HR⟩
  ihave %Hann := typedPointsto_not_null $$ Ha
  ihave Hai : (authInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  icases Hai with ⟨#HeUE, #HeUNF, #HePD, #HeOR, #HeIT, ⟨%s1, #Hs1⟩, ⟨%s2, #Hs2⟩, -⟩
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
  icases Hinv' with ⟨%Hst, -, -, ⟨%be, #Hbe, #Hbeok⟩, -, -, -⟩
  wp_apply wp_with_defer as %defer defer
  (try wp_auto)
  wp_apply (h_IsAuthEnabled st R) $$ [$Hinv $Hen] as %en Hen
  cases en
  · wp_auto
    iapply HΦ
    iunfold authRd
    iframe
    iunfold authErrIs; ileft; ipureintro; rfl
  wp_auto
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
    iunfold authErrIs
    iright
    iexists ErrUserEmpty, eUE
    iframe HeUEa
    ipureintro; simp
  iunfold authBackendOk at Hbeok
  icases Hbeok with ⟨%bi, %Hbi, #HRT⟩
  subst Hbi
  wp_auto
  wp_apply HRT as %tx Htx
  iunfold authReadTxOk at Htx
  icases Htx with ⟨%ti, %Hti, Htx⟩
  subst Hti
  icases Htx with ⟨%Tk, #HRL, #HUG, #HRU⟩
  wp_auto
  wp_bind (App (Val #(methods ti.ty go!"RLock" ti.v)) (Val #()))
  iapply HRL $$ HR
  inext
  iintro Htok
  wp_auto
  wp_bind (App (Val #(methods ti.ty go!"UnsafeGetUser" ti.v)) (Val #info.Username'))
  iapply HUG $$ Htok
  inext
  iintro %u Htok
  ihave Ha : a ↦{dq} info $$ [Username Revision]
  · iapply typedPointsto_combine a info dq Hann
    simp only [TypedPointsto.typedPointstoDef]
    iframe
  wp_auto
  wp_if_destruct
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
    iexists ErrUserNotFound, eUNF
    iframe HeUNFa
    ipureintro; simp
  wp_apply h_hasRootRole $$ [] as %root -
  · ipureintro; assumption
  cases root
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

end proof

end EtcdGrove
end Perennial
