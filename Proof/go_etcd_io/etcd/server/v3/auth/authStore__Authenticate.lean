/-
Proof of the spec of the same name (the auth plan's S5, 2026-10-24). Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.auth.authStore__Authenticate
public import Proof.go_etcd_io.etcd.server.v3.auth.VerdictLemmas
public import Spec.go_etcd_io.etcd.server.v3.auth.authStore__IsAuthEnabled
public import Spec.go_etcd_io.etcd.server.v3.auth.authStore__Revision
public import Spec.go_etcd_io.etcd.server.v3.auth.redactToken
public import Spec.go_uber_org.zap.String
public import Spec.go_uber_org.zap.Logger__Check
public import Spec.go_uber_org.zap.zapcore.CheckedEntry__Write

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.auth auth go_etcd_io.etcd.api.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.auth.Assumptions]

theorem auth.authStore.Authenticate.wp_proof
    (h_IsAuthEnabled : auth.authStore.IsAuthEnabled.spec (GF := GF) (hG := hG))
    (h_Revision : auth.authStore.Revision.spec (GF := GF) (hG := hG))
    (h_redactToken : auth.redactToken.spec (GF := GF) (hG := hG))
    (h_String : zap.String.spec (GF := GF) (hG := hG))
    (h_Check : zap.Logger.Check.spec (GF := GF) (hG := hG))
    (h_Write : zapcore.CheckedEntry.Write.spec (GF := GF) (hG := hG)) :
    auth.authStore.Authenticate.spec (GF := GF) (hG := hG) := by
  intro st R M P f T hs Pre Q Post ctx username password
  wp_start as ⟨#Hinv, Hen, Hown, HWR, Hcs⟩
  icases authErrVar_of_init .authNotEnabled $$ Hpkg with ⟨%eNE, #HeNE⟩
  icases authErrVar_of_init .authFailed $$ Hpkg with ⟨%eAF, #HeAF⟩
  simp only [AuthErr.var]
  ihave #Hzap : isPkgInit (PROP := IProp GF) pkg_id.go_uber_org.zap $$ []
  · iPkgInit
  ihave #Hzapc : isPkgInit (PROP := IProp GF) pkg_id.go_uber_org.zap.zapcore $$ []
  · iPkgInit
  ihave #Hinv' := Hinv
  iunfold authInv at Hinv'
  icases Hinv' with ⟨%Hst, -, ⟨%lg, #Hlg, %Hlgnn⟩, -, ⟨%tp, #Htp, #Htpok⟩, -, -⟩
  iunfold tokenProviderOk at Htpok
  icases Htpok with ⟨%tpi, %Htpi, -, -, -, -, #HAssign⟩
  subst Htpi
  iunfold authWR at HWR
  icases HWR with ⟨⟨%be, Hbe, #Hbeok⟩, HT, Henh⟩
  ihave #Hbeok' := Hbeok
  iunfold authWBackendOk at Hbeok'
  icases Hbeok' with ⟨%bi, %Hbi, -, -, #HGetUser⟩
  subst Hbi
  (try wp_auto)
  wp_apply (h_IsAuthEnabled st R M) $$ [$Hinv $Hen] as %en ⟨Hen, #Hev⟩
  cases en
  · -- auth disabled
    (try wp_auto)
    iapply HΦ
    isplitl [Hcs]
    · iapply csContract_noWrite $$ Hcs
    iframe Hen Hown
    isplitl [Hbe HT Henh]
    · iunfold authWR; iframe HT Henh; iexists (GoInterface.ok bi); iframe Hbe Hbeok
    iunfold authenticated
    ileft; ipureintro; exact ⟨by simp, rfl⟩
  (try wp_auto)
  wp_bind (App (Val #(methods bi.ty go!"GetUser" bi.v)) (Val #username))
  iapply HGetUser $$ %hs %Pre %Q %Post %username [$Hcs $HT $Hown]
  inext
  iintro %u ⟨HPost, HT, Hown, %sta, %Hl, Hu⟩
  (try wp_auto)
  wp_if_destruct
  · -- no such user
    ihave %Hnone := userOut_null sta username $$ Hu
    (try wp_auto)
    iapply HΦ
    isplitl [HPost]
    · ileft; iexact HPost
    iframe Hen Hown
    isplitl [Hbe HT Henh]
    · iunfold authWR; iframe HT Henh; iexists (GoInterface.ok bi); iframe Hbe Hbeok
    iunfold authenticated
    ileft; ipureintro; exact ⟨by simp, rfl⟩
  ihave Hu' := userOut_some u sta username Hif $$ Hu
  icases Hu' with ⟨%roles, %ur, %Hur, Hu⟩
  iunfold ownUser at Hu
  icases Hu with ⟨%s1, %n, %pw, %rl, %o, %uf, %sc, Hp, #Hn, #Hpw, #Hrl, #Ho⟩
  iunfold userOptsAt at Ho
  icases Ho with (%Ho | ⟨%Hon, %s2, %uf2, %sc2, #Hov⟩)
  · obtain ⟨Ho, -⟩ := Ho
    subst Ho
    (try wp_auto)
    (try wp_auto)
    wp_apply (h_Revision st R M (some hs)) $$ [$Hinv Hown] as %rev ⟨Hown, -, -⟩
    · iunfold authOwnOpt; iexact Hown
    iunfold authOwnOpt at Hown
    (try wp_auto)
    wp_bind (App (App (App (Val #(methods tpi.ty go!"assign" tpi.v)) (Val #ctx)) (Val #username)) (Val #rev))
    iapply HAssign $$ %ctx %username %rev
    · itrivial
    inext
    iintro %tok %err Htok
    (try wp_auto)
    cases err with
    | ok ei =>
      (try wp_auto)
      iapply HΦ
      isplitl [HPost]
      · ileft; iexact HPost
      iframe Hen Hown
      isplitl [Hbe HT Henh]
      · iunfold authWR; iframe HT Henh; iexists (GoInterface.ok bi); iframe Hbe Hbeok
      iunfold authenticated
      ileft; ipureintro; exact ⟨by simp, rfl⟩
    | nil =>
      icases Htok with (%Hne | #Htok)
      · exact absurd rfl Hne
      (try wp_auto)
      (try wp_auto)
      wp_apply h_Check as %ce -
      · ipureintro; exact Hlgnn
      (try wp_auto)
      wp_if_destruct
      · -- no entry to write
        (try wp_auto)
        wp_alloc rl as Hrl
        (try wp_auto)
        iapply HΦ
        isplitl [HPost]
        · ileft; iexact HPost
        iframe Hen Hown
        isplitl [Hbe HT Henh]
        · iunfold authWR; iframe HT Henh; iexists (GoInterface.ok bi); iframe Hbe Hbeok
        iunfold authenticated
        iright
        isplitr
        · ipureintro; rfl
        iexists tok, _
        iframe Hrl
        isplitr
        · ipureintro; rfl
        iframe Htok Hev
        ipureintro; exact ⟨sta, Hl, by simp [Hur.1]⟩
      · wp_apply h_redactToken _ as %fp -
        (try wp_auto)
        wp_apply h_String _ _ as %f1 -
        (try wp_auto)
        wp_apply h_String _ _ as %f2 -
        (try wp_auto)
        wp_apply wp_slice_literal (V := go_uber_org.zap.zapcore.Field) [f1, f2]
        isplitr
        · ipureintro; rfl
        iintro %fsl ⟨-, -⟩
        (try wp_auto)
        wp_apply h_Write
        · ipureintro; exact Hif
        (try wp_auto)
        wp_alloc rl as Hrl
        (try wp_auto)
        iapply HΦ
        isplitl [HPost]
        · ileft; iexact HPost
        iframe Hen Hown
        isplitl [Hbe HT Henh]
        · iunfold authWR; iframe HT Henh; iexists (GoInterface.ok bi); iframe Hbe Hbeok
        iunfold authenticated
        iright
        isplitr
        · ipureintro; rfl
        iexists tok, _
        iframe Hrl
        isplitr
        · ipureintro; rfl
        iframe Htok Hev
        ipureintro; exact ⟨sta, Hl, by simp [Hur.1]⟩
  · (try wp_auto)
    have hd : decide (o = null) = false := decide_eq_false Hon
    rw [hd]
    (try wp_auto)
    simp only
    icases typedPointsto_split _ _ _ $$ Hov with Hov
    simp only [TypedPointsto.typedPointstoDef]
    iNamed Hov
    (try wp_auto)
    cases hnp : ur.noPassword
    rotate_left
    · -- a no-password user
      (try wp_auto)
      iapply HΦ
      isplitl [HPost]
      · ileft; iexact HPost
      iframe Hen Hown
      isplitl [Hbe HT Henh]
      · iunfold authWR; iframe HT Henh; iexists (GoInterface.ok bi); iframe Hbe Hbeok
      iunfold authenticated
      ileft; ipureintro; exact ⟨by simp, rfl⟩
    (try wp_auto)
    wp_apply (h_Revision st R M (some hs)) $$ [$Hinv Hown] as %rev ⟨Hown, -, -⟩
    · iunfold authOwnOpt; iexact Hown
    iunfold authOwnOpt at Hown
    (try wp_auto)
    wp_bind (App (App (App (Val #(methods tpi.ty go!"assign" tpi.v)) (Val #ctx)) (Val #username)) (Val #rev))
    iapply HAssign $$ %ctx %username %rev
    · itrivial
    inext
    iintro %tok %err Htok
    (try wp_auto)
    cases err with
    | ok ei =>
      (try wp_auto)
      iapply HΦ
      isplitl [HPost]
      · ileft; iexact HPost
      iframe Hen Hown
      isplitl [Hbe HT Henh]
      · iunfold authWR; iframe HT Henh; iexists (GoInterface.ok bi); iframe Hbe Hbeok
      iunfold authenticated
      ileft; ipureintro; exact ⟨by simp, rfl⟩
    | nil =>
      icases Htok with (%Hne | #Htok)
      · exact absurd rfl Hne
      (try wp_auto)
      (try wp_auto)
      wp_apply h_Check as %ce -
      · ipureintro; exact Hlgnn
      (try wp_auto)
      wp_if_destruct
      · -- no entry to write
        (try wp_auto)
        wp_alloc rl as Hrl
        (try wp_auto)
        iapply HΦ
        isplitl [HPost]
        · ileft; iexact HPost
        iframe Hen Hown
        isplitl [Hbe HT Henh]
        · iunfold authWR; iframe HT Henh; iexists (GoInterface.ok bi); iframe Hbe Hbeok
        iunfold authenticated
        iright
        isplitr
        · ipureintro; rfl
        iexists tok, _
        iframe Hrl
        isplitr
        · ipureintro; rfl
        iframe Htok Hev
        ipureintro; exact ⟨sta, Hl, by simp [Hur.1]⟩
      · wp_apply h_redactToken _ as %fp -
        (try wp_auto)
        wp_apply h_String _ _ as %f1 -
        (try wp_auto)
        wp_apply h_String _ _ as %f2 -
        (try wp_auto)
        wp_apply wp_slice_literal (V := go_uber_org.zap.zapcore.Field) [f1, f2]
        isplitr
        · ipureintro; rfl
        iintro %fsl ⟨-, -⟩
        (try wp_auto)
        wp_apply h_Write
        · ipureintro; exact Hif
        (try wp_auto)
        wp_alloc rl as Hrl
        (try wp_auto)
        iapply HΦ
        isplitl [HPost]
        · ileft; iexact HPost
        iframe Hen Hown
        isplitl [Hbe HT Henh]
        · iunfold authWR; iframe HT Henh; iexists (GoInterface.ok bi); iframe Hbe Hbeok
        iunfold authenticated
        iright
        isplitr
        · ipureintro; rfl
        iexists tok, _
        iframe Hrl
        isplitr
        · ipureintro; rfl
        iframe Htok Hev
        ipureintro; exact ⟨sta, Hl, by simp [Hur.1]⟩

end proof

end EtcdGrove
end Perennial
