/-
Proof of the spec of the same name (the auth plan's S4, 2026-10-24). Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.auth.authStore__UserDelete
public import Proof.go_etcd_io.etcd.server.v3.auth.LatestTie
public import Spec.go_etcd_io.etcd.server.v3.auth.authStore__refreshRangePermCache
public import Spec.go_uber_org.zap.Strings
public import Spec.go_uber_org.zap.Logger__Error
public import Proof.go_etcd_io.etcd.server.v3.auth.VerdictLemmas
public import Spec.go_etcd_io.etcd.server.v3.auth.authStore__commitRevision
public import Spec.go_uber_org.zap.String
public import Spec.go_uber_org.zap.Logger__Info
public import Perennial.Proof.github_com.mit_pdos.perennial.goose.model.strings.Base

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

theorem auth.authStore.UserDelete.wp_tie
    (h_commitRevision : auth.authStore.commitRevision.spec (GF := GF) (hG := hG))
    (h_refresh : auth.authStore.refreshRangePermCache.spec (GF := GF) (hG := hG))
    (h_String : zap.String.spec (GF := GF) (hG := hG))
    (h_Strings : zap.Strings.spec (GF := GF) (hG := hG))
    (h_Error : zap.Logger.Error.spec (GF := GF) (hG := hG))
    (h_Info : zap.Logger.Info.spec (GF := GF) (hG := hG)) :
    auth.authStore.UserDelete.specT (GF := GF) (hG := hG) := by
  intro st R M P f T hs Pre Q Post r name en sc0
  wp_start as ⟨#Hinv, #Hr, Hown, HWR, Htpa, Hcs, %Hok⟩
  icases authErrVar_of_init .userNotFound $$ Hpkg with ⟨%eUNF, #HeUNF⟩
  icases authErrVar_of_init .invalidAuthMgmt $$ Hpkg with ⟨%eIAM, #HeIAM⟩
  simp only [AuthErr.var]
  ihave #Hinv' := Hinv
  iunfold authInv at Hinv'
  icases Hinv' with ⟨%Hst, -, ⟨%lg, #Hlg, %Hlgnn⟩, -, ⟨%tp0, -, -⟩, -, -⟩
  iunfold tpAdmin at Htpa
  icases Htpa with ⟨%tp, %Atp, #Htp, #HtpokA, HA⟩
  ihave #Htpok := HtpokA
  iunfold tokenProviderOkA at Htpok
  icases Htpok with ⟨%tpi, %Htpi, -, -, -, #HInval, -⟩
  subst Htpi
  iunfold userDeleteReqIs at Hr
  icases Hr with ⟨%Hrnn, #HN⟩
  iunfold authWRx at HWR
  icases HWR with ⟨⟨%be, Hbe, #Hbeok⟩, HT, Hen, #Hev, Hca, #Hcsn⟩
  iunfold flagAt at Hen
  ihave #Hbeok' := Hbeok
  iunfold authWBackendOk at Hbeok'
  icases Hbeok' with ⟨%bi, %Hbi, #HBatch, #HFC, -⟩
  subst Hbi
  wp_apply wp_with_defer as %defer defer
  (try wp_auto)
  wp_join (Q := fun v => iprop(⌜v = #(decide (en = true ∧ name = go!"root"))⌝ ∗
      auth.aF go!"enabled" st ↦{DFrac.own (1 : Qp).half} en ∗ r_ptr ↦ r ∗ as_ptr ↦ st))
    at (if: _ then _ else #false) with [Hen r «as»] as ⟨%Hv, Hen, r, «as»⟩
  · cases en
    · (try wp_auto)
      iframe
      ipureintro; simp
    · (try wp_auto)
      iframe
      ipureintro; simp
  subst Hv
  wp_if_destruct
  · -- `root` with auth enabled: refused
    obtain ⟨Hen1, Hroot⟩ := Hif
    subst Hen1
    (try wp_auto)
    wp_apply h_String _ _ as %f1 -
    (try wp_auto)
    wp_apply wp_slice_literal (V := go_uber_org.zap.zapcore.Field) [f1]
    isplitr
    · ipureintro; rfl
    iintro %fsl ⟨-, -⟩
    (try wp_auto)
    wp_apply h_Error
    · ipureintro; exact Hlgnn
    (try wp_auto)
    iapply HΦ
    iexists true, sc0

    isplitl [HA]

    · iunfold tpAdmin; iexists (GoInterface.ok tpi), Atp; iframe HA; iframe #
    isplitl [Hcs]
    · iapply csContract_noWrite $$ Hcs
    isplitl [Hbe HT Hen Hca]
    · iunfold authWRx; iunfold flagAt; iframe HT Hen Hev Hca Hcsn; iexists (GoInterface.ok bi); iframe Hbe Hbeok
    isplitr
    · iunfold respOk; isplitr
      · ipureintro; intro _; rfl
      · ileft; ipureintro; rfl
    iexists true
    iframe Hev
    iunfold adminOutP
    iright
    ihave %Hl := authOwn_exists_last M hs $$ Hown
    obtain ⟨st0, Hl⟩ := Hl
    iexists st0, (.err .invalidAuthMgmt)
    isplitr
    · ipureintro; exact tieStep_same _ _ _ _
    isplitr
    · ipureintro
      refine ⟨Hl, ?_⟩
      simp [stepOf, userDeleteF, rootRole, Hroot]
    simp only [outRes]
    iframe Hown
    simp only [authErrOf, AuthErr.var]; iexists eIAM; iframe HeIAM; ipureintro; rfl
  have hnr : ¬ (en = true ∧ name = rootRole) := Hif
  clear Hif
  wp_apply HBatch as %tx Htx
  iunfold authBatchTxOk at Htx
  icases Htx with ⟨%ti, %Hti, %Lk, #HLk⟩
  subst Hti
  ihave #HLk' := HLk
  iunfold authBatchTxLk at HLk'
  icases HLk' with ⟨#HLock, #HRd, -, #HDelU, -, -, -, -, #HUnlock, -, -⟩
  (try wp_auto)
  wp_bind (App (Val #(methods ti.ty go!"Lock" ti.v)) (Val #()))
  iapply HLock $$ %hs %Pre %Q %Post [$Hcs $HT $Hown]
  inext
  iintro ⟨%st0, HL, Hown, %Hl0⟩
  ihave #HRd' := HRd $$ %Post
  iunfold authReaderOk at HRd'
  icases HRd' with ⟨#HUG, -, -, -, -⟩
  (try wp_auto)
  wp_bind (App (Val #(methods ti.ty go!"UnsafeGetUser" ti.v)) (Val #name))
  iapply HUG $$ %st0 %name HL
  inext
  iintro %u ⟨HL, Hu⟩
  (try wp_auto)
  wp_if_destruct
  · -- no such user
    ihave %Hnone := userOut_null st0 name $$ Hu
    wp_apply HUnlock $$ %st0 %Post %hs [$HL $Hown] as ⟨HPost, HT, Hown⟩
    · ipureintro; exact Hl0
    (try wp_auto)
    iapply HΦ
    iexists en, sc0

    isplitl [HA]

    · iunfold tpAdmin; iexists (GoInterface.ok tpi), Atp; iframe HA; iframe #
    isplitl [HPost]
    · ileft; iexact HPost
    isplitl [Hbe HT Hen Hca]
    · iunfold authWRx; iunfold flagAt; iframe HT Hen Hev Hca Hcsn; iexists (GoInterface.ok bi); iframe Hbe Hbeok
    isplitr
    · iunfold respOk; isplitr
      · ipureintro; intro _; rfl
      · ileft; ipureintro; rfl
    iexists en
    iframe Hev
    iunfold adminOutP
    iright
    iexists st0, (.err .userNotFound)
    isplitr
    · ipureintro; exact tieStep_same _ _ _ _
    isplitr
    · ipureintro
      refine ⟨Hl0, ?_⟩
      simp [stepOf, userDeleteF, hnr, Hnone]
    simp only [outRes, authErrOf, AuthErr.var]
    iframe Hown
    iexists eUNF; iframe HeUNF; ipureintro; rfl
  ihave Hu' := userOut_some _ st0 name Hif $$ Hu
  icases Hu' with ⟨%roles, %ur, %Hur, Hu⟩
  ihave %Hpk := authOwnF_last_permKeysOk M hs $$ Hown
  have Hstep := (Hok en st0 Hl0)
  wp_bind (App (Val #(methods ti.ty go!"UnsafeDeleteUser" ti.v)) (Val #name))
  iapply HDelU $$ %st0 %Post %name HL
  inext
  iintro HL
  (try wp_auto)
  have hstep : userDeleteF en name st0 = .next (bump (delUser st0 name)) := by
    simp [userDeleteF, hnr, Hur.1]
  obtain ⟨Hrevfit, Hfit⟩ := Hstep
  have Hfit' := Hfit _ _ rfl hstep
  wp_apply (h_commitRevision st R M P f T ti Lk (delUser st0 name) Post hs st0)
    $$ [$Hinv $HLk $HL $Hown] as ⟨%rev, %Hrev, HL, Hown⟩
  · ipureintro
    refine ⟨Hl0, rfl, Hrevfit, fun h1 h2 => permKeysOk_delUser _ _ (Hpk st0 Hl0 h1 h2), ?_⟩
    intro hM; subst hM; exact Hl0
  have Hl1 := histLast_after M hs (delUser st0 name) rev (fun h => by subst h; exact Hl0) Hrev
  imod (authSnapF_of_last M _ _ Hl1) $$ Hown with ⟨Hown, #Hsnap⟩
  (try wp_auto)
  wp_bind (App (Val (st @!! go.GoType.PointerType authStore.ty @!! go!"refreshRangePermCache"))
    (Val #(GoInterface.ok ti)))
  iapply (h_refresh st R M ti (fun x => Lk x Post) ({ delUser st0 name with revision := rev } : AuthState))
    $$ [HL Hca]
  · iframe Hpkg Hinv
    isplitl [Hca]
    · iapply (cacheHalf_of_at _ _ _) $$ Hca Hcsn
    isplitr
    · iapply HRd
    isplitl [HL]
    · iExactEq HL
      all_goals rfl
    iframe Hsnap
    ipureintro; exact permsFit_rev _ rev Hfit'
  inext
  iintro ⟨HL, Hca⟩
  (try wp_auto)
  wp_bind (App (Val #(methods tpi.ty go!"invalidateUser" tpi.v)) (Val #name))
  iapply HInval $$ %name [HA] [-]
  · iexact HA
  inext
  iintro HA
  iunfold ownUser at Hu
  icases Hu with ⟨%ums, %unm, %upw, %url, %uo, %uuf, %usc, Hup, -, -, -, -⟩
  icases typedPointsto_split _ _ _ $$ Hup with Hup
  simp only [TypedPointsto.typedPointstoDef]
  iNamed Hup
  (try wp_auto)
  wp_apply h_String _ _ as %f1 -
  (try wp_auto)
  wp_apply h_Strings _ _ as %f2 -
  (try wp_auto)
  wp_apply wp_slice_literal (V := go_uber_org.zap.zapcore.Field) [f1, f2]
  isplitr
  · ipureintro; rfl
  iintro %fsl ⟨-, -⟩
  (try wp_auto)
  wp_apply h_Info
  · ipureintro; exact Hlgnn
  (try wp_auto)
  wp_alloc resp as Hresp
  icases typedPointsto_split _ _ _ $$ Hresp with Hresp
  simp only [TypedPointsto.typedPointstoDef]
  iNamed Hresp
  (try wp_auto)
  wp_apply HUnlock $$ %_ %Post %(hs ++ [bump (delUser st0 name)]) [HL $Hown]
    as ⟨HPost, HT, Hown⟩
  · isplitl [HL]
    · iExactEq HL
      all_goals rfl
    ipureintro; exact Hl1
  (try wp_auto)
  iapply HΦ
  iexists en, ({ delUser st0 name with revision := rev } : AuthState)

  isplitl [HA]

  · iunfold tpAdmin; iexists (GoInterface.ok tpi), Atp; iframe HA; iframe #
  isplitl [HPost]
  · ileft; iexact HPost
  isplitl [Hbe HT Hen Hca]
  · iunfold authWRx; iunfold flagAt; iframe HT Hen Hev Hca Hsnap; iexists (GoInterface.ok bi); iframe Hbe Hbeok
  isplitl [Header]
  · iunfold respOk; isplitr
    · ipureintro; intro h; exact absurd rfl h
    · iright; iexists _; iexact Header
  iexists en
  iframe Hev
  iunfold adminOutP
  iright
  iexists st0, (.next (bump (delUser st0 name)))
  isplitr
  · ipureintro; exact tieStep_refresh M hs _ _ sc0 _ st0 Hl0 Hl1 rfl
  isplitr
  · ipureintro; exact ⟨Hl0, hstep.symm⟩
  simp only [outRes]
  isplitl [Hown]
  · iExactEq Hown
    all_goals rfl
  · ipureintro; trivial


theorem auth.authStore.UserDelete.wp_proof
    (h_commitRevision : auth.authStore.commitRevision.spec (GF := GF) (hG := hG))
    (h_refresh : auth.authStore.refreshRangePermCache.spec (GF := GF) (hG := hG))
    (h_String : zap.String.spec (GF := GF) (hG := hG))
    (h_Strings : zap.Strings.spec (GF := GF) (hG := hG))
    (h_Error : zap.Logger.Error.spec (GF := GF) (hG := hG))
    (h_Info : zap.Logger.Info.spec (GF := GF) (hG := hG)) :
    auth.authStore.UserDelete.spec (GF := GF) (hG := hG) :=
  auth.authStore.UserDelete.spec_of_T (auth.authStore.UserDelete.wp_tie h_commitRevision h_refresh h_String h_Strings h_Error h_Info)

end proof

end EtcdGrove
end Perennial
