/-
Proof of the spec of the same name (the auth plan's S4, 2026-10-24). Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.auth.authStore__AuthEnable
public import Proof.go_etcd_io.etcd.server.v3.auth.LatestTie
public import Spec.go_etcd_io.etcd.server.v3.auth.authStore__refreshRangePermCache
public import Spec.go_etcd_io.etcd.server.v3.auth.authStore__setRevision
public import Spec.go_etcd_io.etcd.server.v3.auth.hasRootRole
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

theorem auth.authStore.AuthEnable.wp_tie
    (h_refresh : auth.authStore.refreshRangePermCache.spec (GF := GF) (hG := hG))
    (h_setRevision : auth.authStore.setRevision.spec (GF := GF) (hG := hG))
    (h_hasRootRole : auth.hasRootRole.spec (GF := GF) (hG := hG))
    (h_Info : zap.Logger.Info.spec (GF := GF) (hG := hG)) :
    auth.authStore.AuthEnable.specT (GF := GF) (hG := hG) := by
  intro st R M P f T hs Pre Q Post en sc0
  wp_start as ⟨#Hinv, %HisOn, Hown, HWR, Htpa, Hcs, %Hok⟩
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  icases authErrVar_of_init .rootUserNotExist $$ Hpkg with ⟨%eRUN, #HeRUN⟩
  icases authErrVar_of_init .rootRoleNotExist $$ Hpkg with ⟨%eRRN, #HeRRN⟩
  simp only [AuthErr.var]
  ihave #Hinv' := Hinv
  iunfold authInv at Hinv'
  icases Hinv' with ⟨%Hst, -, ⟨%lg, #Hlg, %Hlgnn⟩, -, ⟨%tp0, -, -⟩, #Hguard, -⟩
  iunfold tpAdmin at Htpa
  icases Htpa with ⟨%tp, %Atp, #Htp, #HtpokA, HA⟩
  ihave #Htpok := HtpokA
  iunfold tokenProviderOkA at Htpok
  icases Htpok with ⟨%tpi, %Htpi, -, #HEnable, -, -, -⟩
  subst Htpi
  iunfold authWRx at HWR
  icases HWR with ⟨⟨%be, Hbe, #Hbeok⟩, HT, Hen, #Hev, Hca, #Hcsn⟩
  iunfold flagAt at Hen
  ihave #Hbeok' := Hbeok
  iunfold authWBackendOk at Hbeok'
  icases Hbeok' with ⟨%bi, %Hbi, #HBatch, #HFC, -⟩
  subst Hbi
  wp_apply wp_with_defer as %defer defer
  (try wp_auto)
  wp_apply sync.RWMutex.wp_Lock_guard $$ [$Hguard] as ⟨Hlk, HP⟩
  iunfold enabledP at HP
  icases HP with ⟨%en', Hen', #Hev'⟩
  icombine Hen Hen' gives %Heq
  subst Heq
  ihave Hen := (typedPointsto_half_split _ _ (1 : Qp)).2 $$ [Hen Hen']
  · iframe
  (try wp_auto)
  cases en
  rotate_left
  · -- enabled already: nothing
    (try wp_auto)
    wp_apply h_Info
    · ipureintro; exact Hlgnn
    (try wp_auto)
    ihave ⟨Hen, Hen'⟩ := (typedPointsto_half_split _ _ (1 : Qp)).1 $$ Hen
    wp_apply sync.RWMutex.wp_Unlock_guard $$ [$Hlk Hen']
    · inext; iunfold enabledP; iexists true; iframe Hen'; iexact Hev
    (try wp_auto)
    iapply HΦ
    iexists true, sc0

    isplitl [HA]

    · iunfold tpAdmin; iexists (GoInterface.ok tpi), Atp; iframe HA; iframe #
    isplitl [Hcs]
    · iapply csContract_noWrite $$ Hcs
    isplitl [Hbe HT Hen Hca]
    · iunfold authWRx; iunfold flagAt; iframe HT Hen Hev Hca Hcsn; iexists (GoInterface.ok bi); iframe Hbe Hbeok
    iexists true
    iframe Hev
    iunfold adminOutP
    iright
    ihave %Hl := authOwn_exists_last M hs $$ Hown
    obtain ⟨st0, Hl⟩ := Hl
    iexists st0, .same
    isplitr
    · ipureintro; exact tieStep_same _ _ _ _
    isplitr
    · ipureintro
      refine ⟨Hl, ?_⟩
      simp [stepOf, authEnableF]
    simp only [outRes]
    iframe Hown
  (try wp_auto)
  wp_apply HBatch as %tx Htx
  iunfold authBatchTxOk at Htx
  icases Htx with ⟨%ti, %Hti, %Lk, #HLk⟩
  subst Hti
  ihave #HLk' := HLk
  iunfold authBatchTxLk at HLk'
  icases HLk' with ⟨#HLock, #HRd, -, -, -, -, #HSaveEn, -, #HUnlock, -, -⟩
  (try wp_auto)
  wp_bind (App (Val #(methods ti.ty go!"Lock" ti.v)) (Val #()))
  iapply HLock $$ %hs %Pre %Q %Post [$Hcs $HT $Hown]
  inext
  iintro ⟨%st0, HL, Hown, %Hl0⟩
  ihave %Hpk := authOwnF_last_permKeysOk M hs $$ Hown
  have Hstep := (Hok false st0 Hl0)
  ihave #HRd' := HRd $$ %Post
  iunfold authReaderOk at HRd'
  icases HRd' with ⟨#HUG, -, -, #HRR, -⟩
  (try wp_auto)
  wp_bind (App (Val #(methods ti.ty go!"UnsafeGetUser" ti.v)) (Val #(go!"root")))
  iapply HUG $$ %st0 %(go!"root") HL
  inext
  iintro %u ⟨HL, Hu⟩
  (try wp_auto)
  wp_if_destruct
  · -- no root user
    ihave %Hnone := userOut_null st0 (go!"root") $$ Hu
    (try wp_auto)
    wp_apply HUnlock $$ %st0 %Post %hs [$HL $Hown] as ⟨HPost, HT, Hown⟩
    · ipureintro; exact Hl0
    (try wp_auto)
    wp_bind (App (Val #(methods bi.ty go!"ForceCommit" bi.v)) (Val #()))
    iapply HFC $$ HT
    inext
    iintro HT
    (try wp_auto)
    ihave ⟨Hen, Hen'⟩ := (typedPointsto_half_split _ _ (1 : Qp)).1 $$ Hen
    wp_apply sync.RWMutex.wp_Unlock_guard $$ [$Hlk Hen']
    · inext; iunfold enabledP; iexists false; iframe Hen'; iexact Hev
    (try wp_auto)
    iapply HΦ
    iexists false, sc0

    isplitl [HA]

    · iunfold tpAdmin; iexists (GoInterface.ok tpi), Atp; iframe HA; iframe #
    isplitl [HPost]
    · ileft; iexact HPost
    isplitl [Hbe HT Hen Hca]
    · iunfold authWRx; iunfold flagAt; iframe HT Hen Hev Hca Hcsn; iexists (GoInterface.ok bi); iframe Hbe Hbeok
    iexists false
    iframe Hev
    iunfold adminOutP
    iright
    iexists st0, (.err .rootUserNotExist)
    isplitr
    · ipureintro; exact tieStep_same _ _ _ _
    isplitr
    · ipureintro
      refine ⟨Hl0, ?_⟩
      have : st0.users !! rootRole = none := Hnone
      simp [stepOf, authEnableF, this]
    simp only [outRes, authErrOf, AuthErr.var]
    iframe Hown
    iexists eRUN; iframe HeRUN; ipureintro; rfl
  ihave Hu' := userOut_some _ st0 (go!"root") Hif $$ Hu
  icases Hu' with ⟨%roles, %ur, %Hur, Hu⟩
  wp_apply h_hasRootRole $$ [$Hu] as %root ⟨Hu, %Hroot⟩
  · ipureintro; rw [Hur.2.1]; exact Hur.2.2
  have hroot : st0.users !! rootRole = some roles := Hur.1
  cases root
  · -- the root user lacks the root role
    have hn : ¬ isRoot roles := by rw [← Hur.2.1]; exact of_decide_eq_false Hroot.symm
    simp only [Bool.not_false]
    (try wp_auto)
    wp_apply HUnlock $$ %st0 %Post %hs [$HL $Hown] as ⟨HPost, HT, Hown⟩
    · ipureintro; exact Hl0
    (try wp_auto)
    wp_bind (App (Val #(methods bi.ty go!"ForceCommit" bi.v)) (Val #()))
    iapply HFC $$ HT
    inext
    iintro HT
    (try wp_auto)
    ihave ⟨Hen, Hen'⟩ := (typedPointsto_half_split _ _ (1 : Qp)).1 $$ Hen
    wp_apply sync.RWMutex.wp_Unlock_guard $$ [$Hlk Hen']
    · inext; iunfold enabledP; iexists false; iframe Hen'; iexact Hev
    (try wp_auto)
    iapply HΦ
    iexists false, sc0

    isplitl [HA]

    · iunfold tpAdmin; iexists (GoInterface.ok tpi), Atp; iframe HA; iframe #
    isplitl [HPost]
    · ileft; iexact HPost
    isplitl [Hbe HT Hen Hca]
    · iunfold authWRx; iunfold flagAt; iframe HT Hen Hev Hca Hcsn; iexists (GoInterface.ok bi); iframe Hbe Hbeok
    iexists false
    iframe Hev
    iunfold adminOutP
    iright
    iexists st0, (.err .rootRoleNotExist)
    isplitr
    · ipureintro; exact tieStep_same _ _ _ _
    isplitr
    · ipureintro
      refine ⟨Hl0, ?_⟩
      simp [stepOf, authEnableF, hroot, hn]
    simp only [outRes, authErrOf, AuthErr.var]
    iframe Hown
    iexists eRRN; iframe HeRRN; ipureintro; rfl
  have hr : isRoot roles := by rw [← Hur.2.1]; exact of_decide_eq_true Hroot.symm
  have hstep : authEnableF false st0 = .next { st0 with enabled := true } := by
    simp [authEnableF, hroot, hr]
  have Hfit := Hstep.2 _ _ rfl hstep
  simp only [Bool.not_true]
  (try wp_auto)
  wp_bind (App (Val #(methods ti.ty go!"UnsafeSaveAuthEnabled" ti.v)) (Val #true))
  iapply HSaveEn $$ %st0 %Post %true HL
  inext
  iintro HL
  (try wp_auto)
  wp_bind (App (Val #(methods tpi.ty go!"enable" tpi.v)) (Val #()))
  iapply HEnable $$ [HA] [-]
  · iexact HA
  inext
  iintro HA
  (try wp_auto)
  -- the new state appended (the revision unchanged), and recorded
  have hoff : M = .off → ({ st0 with enabled := true } : AuthState).enabled = false := by
    intro h; subst h; cases HisOn
  imod (authOwnF_append_same st R M hs st0 { st0 with enabled := true } Hl0 rfl
    (fun h1 h2 => permKeysOk_enabled _ _ (Hpk st0 Hl0 h1 h2)) hoff) $$ Hinv Hown with Hown
  have Hl1 : histLast M (hs ++ [{ st0 with enabled := true }]) { st0 with enabled := true } := by
    cases M with
    | on γa => simp [histLast]
    | off => cases HisOn
    | any => trivial
  imod (authSnapF_of_last M _ _ Hl1) $$ Hown with ⟨Hown, #Hsnap⟩
  ihave #Hev2 := enabledVerdict_of_snap M _ $$ Hsnap
  wp_bind (App (Val (st @!! go.GoType.PointerType authStore.ty @!! go!"refreshRangePermCache"))
    (Val #(GoInterface.ok ti)))
  iapply (h_refresh st R M ti (fun x => Lk x Post) ({ st0 with enabled := true } : AuthState))
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
    ipureintro; exact Hfit
  inext
  iintro ⟨HL, Hca⟩
  (try wp_auto)
  wp_bind (App (Val #(methods ti.ty go!"UnsafeReadAuthRevision" ti.v)) (Val #()))
  iapply HRR $$ %({ st0 with enabled := true } : AuthState) HL
  inext
  iintro %rv ⟨HL, %Hrv⟩
  (try wp_auto)
  wp_apply (h_setRevision st R M rv (hs ++ [{ st0 with enabled := true }]) [] { st0 with enabled := true })
    $$ [$Hinv Hown] as Hown
  · isplitl [Hown]
    · iExactEq Hown
      all_goals simp
    ipureintro
    refine ⟨by simpa using Hl1, Hrv, by simp, by simp⟩
  (try wp_auto)
  wp_apply h_Info
  · ipureintro; exact Hlgnn
  (try wp_auto)
  simp only [List.append_nil]
  wp_apply HUnlock $$ %_ %Post %(hs ++ [{ st0 with enabled := true }]) [HL $Hown]
    as ⟨HPost, HT, Hown⟩
  · isplitl [HL]
    · iExactEq HL
      all_goals rfl
    ipureintro; exact Hl1
  (try wp_auto)
  wp_bind (App (Val #(methods bi.ty go!"ForceCommit" bi.v)) (Val #()))
  iapply HFC $$ HT
  inext
  iintro HT
  (try wp_auto)
  ihave ⟨Hen, Hen'⟩ := (typedPointsto_half_split _ _ (1 : Qp)).1 $$ Hen
  wp_apply sync.RWMutex.wp_Unlock_guard $$ [$Hlk Hen']
  · inext; iunfold enabledP; iexists true; iframe Hen'; iexact Hev2
  (try wp_auto)
  iapply HΦ
  iexists true, ({ st0 with enabled := true } : AuthState)

  isplitl [HA]

  · iunfold tpAdmin; iexists (GoInterface.ok tpi), Atp; iframe HA; iframe #
  isplitl [HPost]
  · ileft; iexact HPost
  isplitl [Hbe HT Hen Hca]
  · iunfold authWRx; iunfold flagAt; iframe HT Hen Hev2 Hca Hsnap; iexists (GoInterface.ok bi); iframe Hbe Hbeok
  iexists false
  iframe Hev
  iunfold adminOutP
  iright
  iexists st0, (.next { st0 with enabled := true })
  isplitr
  · ipureintro; exact tieStep_set M hs _ _ _ true _ _ Hl1 rfl (fun _ => rfl)
  isplitr
  · ipureintro; exact ⟨Hl0, hstep.symm⟩
  simp only [outRes]
  isplitl [Hown]
  · iExactEq Hown
    all_goals rfl
  · ipureintro; trivial


theorem auth.authStore.AuthEnable.wp_proof
    (h_refresh : auth.authStore.refreshRangePermCache.spec (GF := GF) (hG := hG))
    (h_setRevision : auth.authStore.setRevision.spec (GF := GF) (hG := hG))
    (h_hasRootRole : auth.hasRootRole.spec (GF := GF) (hG := hG))
    (h_Info : zap.Logger.Info.spec (GF := GF) (hG := hG)) :
    auth.authStore.AuthEnable.spec (GF := GF) (hG := hG) :=
  auth.authStore.AuthEnable.spec_of_T (auth.authStore.AuthEnable.wp_tie h_refresh h_setRevision h_hasRootRole h_Info)

end proof

end EtcdGrove
end Perennial
