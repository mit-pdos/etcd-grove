/-
Proof of `Spec/go_etcd_io/etcd/server/v3/auth/WithRootInternal.lean` (etcd-io/etcd#22493,
`pr-verify/etcd-22493`). Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.auth.WithRootInternal
public import Spec.go_etcd_io.etcd.server.v3.auth.authStore__IsAuthEnabled
public import Spec.go_etcd_io.etcd.server.v3.auth.authStore__Revision
public import Spec.go_etcd_io.etcd.server.v3.auth.authStore__WithRoot
public import Spec.context.WithValueInternalRoot

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.auth auth

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.auth.Assumptions]

theorem auth.WithRootInternal.wp_proof
    (h_IsAuthEnabled : auth.authStore.IsAuthEnabled.spec (GF := GF) (hG := hG))
    (h_Revision : auth.authStore.Revision.spec (GF := GF) (hG := hG))
    (h_WithRoot : auth.authStore.WithRoot.spec (GF := GF) (hG := hG))
    (h_WithValue : context.WithValueInternalRoot.spec (GF := GF) (hG := hG)) :
    auth.WithRootInternal.spec (GF := GF) (hG := hG) := by
  intro st R ctx
  wp_start as ⟨#Hinv, Hen⟩
  ihave #Hctxpkg : isPkgInit (PROP := IProp GF) pkg_id.context $$ []
  · iPkgInit
  ihave #Hinv' := Hinv
  iunfold authInv at Hinv'
  icases Hinv' with ⟨%Hst, -, -, -, ⟨%tp, #Htp, #Htpok⟩, -, -⟩
  ihave #Htpok' := Htpok
  iunfold tokenProviderOk at Htpok'
  icases Htpok' with ⟨%ti, %Hti, %Htip, -⟩
  subst Hti
  wp_auto
  by_cases hj : ti.ty = go.GoType.PointerType tokenJWT.ty
  · simp only [hj, decide_true]
    wp_auto
    wp_apply (h_IsAuthEnabled st R) $$ [$Hinv $Hen] as %en Hen
    cases en
    · wp_auto
      wp_apply (h_WithRoot st R ctx) $$ [$Hinv $Hen] as %c ⟨Hen, %c', %Hc, #Hd, #Hk⟩
      iapply HΦ
      iframe Hen
      iexists c'
      isplitr
      · ipureintro; exact Hc
      isplitr
      · iexact Hd
      iright
      iexact Hk
    · wp_auto
      wp_apply (h_Revision st R) $$ [$Hinv] as %rev -
      (try wp_auto)
      wp_apply (h_WithValue ctx (internalRootContextValue.mk st rev)) $$ [] as %c ⟨%c', %Hc, #Hr, #Hd⟩
      iapply HΦ
      iframe Hen
      iexists c'
      isplitr
      · ipureintro; exact Hc
      isplitr
      · iexact Hd
      ileft
      isplitr
      · iunfold jwtProvider
        iexists (GoInterface.ok ti), ti
        isplitr
        · iexact Htp
        ipureintro; exact ⟨rfl, hj⟩
      iexists rev
      iexact Hr
  · simp only [hj, decide_false]
    wp_auto
    wp_apply (h_WithRoot st R ctx) $$ [$Hinv $Hen] as %c ⟨Hen, %c', %Hc, #Hd, #Hk⟩
    iapply HΦ
    iframe Hen
    iexists c'
    isplitr
    · ipureintro; exact Hc
    isplitr
    · iexact Hd
    iright
    iexact Hk
end proof

end EtcdGrove
end Perennial
