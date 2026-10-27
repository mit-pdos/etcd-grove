/-
Proof of the spec of the same name (the auth plan's S4, 2026-10-24). Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.auth.authStore__AuthDisable
public import Proof.go_etcd_io.etcd.server.v3.auth.LatestTie
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
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.auth.Assumptions]

theorem auth.authStore.AuthDisable.wp_tie
    (h_commitRevision : auth.authStore.commitRevision.spec (GF := GF) (hG := hG))
    (h_Info : zap.Logger.Info.spec (GF := GF) (hG := hG)) :
    auth.authStore.AuthDisable.specT (GF := GF) (hG := hG) := by
  intro st R M P f T hs Pre Q Post en sc0
  wp_start as ⟨#Hinv, Hown, HWR, Htpa, Hcs, %Hok⟩
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  ihave #Hinv' := Hinv
  iunfold authInv at Hinv'
  icases Hinv' with ⟨%Hst, -, ⟨%lg, #Hlg, %Hlgnn⟩, -, ⟨%tp0, -, -⟩, #Hguard, -⟩
  iunfold tpAdmin at Htpa
  icases Htpa with ⟨%tp, %Atp, #Htp, #HtpokA, HA⟩
  ihave #Htpok := HtpokA
  iunfold tokenProviderOkA at Htpok
  icases Htpok with ⟨%tpi, %Htpi, -, -, #HDisable, -, -⟩
  subst Htpi
  iunfold authWRx at HWR
  icases HWR with ⟨⟨%be, Hbe, #Hbeok⟩, HT, Hen, #Hev, Hca, #Hcsn⟩
  iunfold flagAt at Hen
  icases Hen with ⟨Hen, HenQ⟩
  ihave #Hbeok' := Hbeok
  iunfold authWBackendOk at Hbeok'
  icases Hbeok' with ⟨%bi, %Hbi, #HBatch, #HFC, -⟩
  subst Hbi
  wp_apply wp_with_defer as %defer defer
  (try wp_auto)
  wp_apply sync.RWMutex.wp_Lock_guard $$ [$Hguard] as ⟨Hlk, HP⟩
  iunfold enabledP at HP
  icases HP with ⟨%en', Hen', #Hev', Hg⟩
  icombine Hen Hen' gives %Heq
  subst Heq
  ihave Hen := (typedPointsto_half_split _ _ (1 : Qp)).2 $$ [Hen Hen']
  · iframe
  (try wp_auto)
  cases en
  · -- disabled already: nothing
    (try wp_auto)
    ihave ⟨Hen, Hen'⟩ := (typedPointsto_half_split _ _ (1 : Qp)).1 $$ Hen
    (try wp_auto)
    wp_apply sync.RWMutex.wp_Unlock_guard $$ [$Hlk Hen' Hg]
    · inext; iunfold enabledP; iexists false; iframe Hen' Hg; iexact Hev
    (try wp_auto)
    iapply HΦ
    iexists false, sc0

    isplitl [HA]

    · iunfold tpAdmin; iexists (GoInterface.ok tpi), Atp; iframe HA; iframe #
    isplitl [Hcs]
    · iapply csContract_noWrite $$ Hcs
    isplitl [Hbe HT Hen HenQ Hca]
    · iunfold authWRx; iunfold flagAt; iframe HT Hen HenQ Hev Hca Hcsn; iexists (GoInterface.ok bi); iframe Hbe Hbeok
    iexists false
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
      simp [stepOf, authDisableF]
    simp only [outRes]
    iframe Hown
  -- enabled: disable it
  simp only [Bool.not_true]
  (try wp_auto)
  wp_apply HBatch as %tx Htx
  iunfold authBatchTxOk at Htx
  icases Htx with ⟨%ti, %Hti, %Lk, #HLk⟩
  subst Hti
  ihave #HLk' := HLk
  iunfold authBatchTxLk at HLk'
  icases HLk' with ⟨#HLock, -, -, -, -, -, #HSaveEn, -, #HUnlock, -, -⟩
  (try wp_auto)
  wp_bind (App (Val #(methods ti.ty go!"Lock" ti.v)) (Val #()))
  iapply HLock $$ %hs %Pre %Q %Post [$Hcs $HT $Hown]
  inext
  iintro ⟨%st0, HL, Hown, %Hl0⟩
  ihave %Hpk := authOwnF_last_permKeysOk M hs $$ Hown
  have Hstep := (Hok true st0 Hl0)
  (try wp_auto)
  wp_bind (App (Val #(methods ti.ty go!"UnsafeSaveAuthEnabled" ti.v)) (Val #false))
  iapply HSaveEn $$ %st0 %Post %false HL
  inext
  iintro HL
  (try wp_auto)
  have hstep : authDisableF true st0 = .next (bump { st0 with enabled := false }) := rfl
  obtain ⟨Hrevfit, Hfit⟩ := Hstep
  have Hoff : M = .off → ({ st0 with enabled := false } : AuthState).enabled = false := fun _ => rfl
  wp_apply (h_commitRevision st R M P f T ti Lk { st0 with enabled := false } Post hs st0)
    $$ [$Hinv $HLk $HL $Hown] as ⟨%rev, %Hrev, HL, Hown⟩
  · ipureintro
    exact ⟨Hl0, rfl, Hrevfit, fun h1 h2 => permKeysOk_enabled _ _ (Hpk st0 Hl0 h1 h2), Hoff⟩
  have Hl1 := histLast_after M hs { st0 with enabled := false } rev (fun _ => rfl) Hrev
  imod (authSnapF_of_last M _ _ Hl1) $$ Hown with ⟨Hown, #Hsnap⟩
  ihave #Hev2 := enabledVerdict_of_snap M _ $$ Hsnap
  (try wp_auto)
  wp_apply HUnlock $$ %_ %Post %(hs ++ [bump { st0 with enabled := false }]) [HL $Hown]
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
  wp_bind (App (Val #(methods tpi.ty go!"disable" tpi.v)) (Val #()))
  iapply HDisable $$ [HA] [-]
  · iexact HA
  inext
  iintro HA
  (try wp_auto)
  wp_apply h_Info
  · ipureintro; exact Hlgnn
  (try wp_auto)
  ihave ⟨Hen, Hen'⟩ := (typedPointsto_half_split _ _ (1 : Qp)).1 $$ Hen
  -- (E3h) the field's ghost variable set to the new latest state's flag
  imod (enG_update st R M (hs ++ [bump { st0 with enabled := false }]) true false
    (fun γa stl _ hl => by
      simp only [List.getLast?_append, List.getLast?_singleton, Option.some_or,
        Option.some.injEq] at hl
      subst hl; rfl)) $$ Hinv Hown Hg HenQ with ⟨Hown, Hg, HenQ⟩
  wp_apply sync.RWMutex.wp_Unlock_guard $$ [$Hlk Hen' Hg]
  · inext; iunfold enabledP; iexists false; iframe Hen' Hg; iexact Hev2
  (try wp_auto)
  iapply HΦ
  iexists false, sc0

  isplitl [HA]

  · iunfold tpAdmin; iexists (GoInterface.ok tpi), Atp; iframe HA; iframe #
  isplitl [HPost]
  · ileft; iexact HPost
  isplitl [Hbe HT Hen HenQ Hca]
  · iunfold authWRx; iunfold flagAt; iframe HT Hen HenQ Hev2 Hca Hcsn; iexists (GoInterface.ok bi); iframe Hbe Hbeok
  iexists true
  iframe Hev
  iunfold adminOutP
  iright
  iexists st0, (.next (bump { st0 with enabled := false }))
  isplitr
  · ipureintro; exact tieStep_setKeep M hs _ _ sc0 st0 false _ Hl0 Hl1 rfl (fun h => by cases h) rfl
  isplitr
  · ipureintro; exact ⟨Hl0, hstep.symm⟩
  simp only [outRes]
  isplitl [Hown]
  · iExactEq Hown
    all_goals rfl
  · ipureintro; trivial


theorem auth.authStore.AuthDisable.wp_proof
    (h_commitRevision : auth.authStore.commitRevision.spec (GF := GF) (hG := hG))
    (h_Info : zap.Logger.Info.spec (GF := GF) (hG := hG)) :
    auth.authStore.AuthDisable.spec (GF := GF) (hG := hG) :=
  auth.authStore.AuthDisable.spec_of_T (auth.authStore.AuthDisable.wp_tie h_commitRevision h_Info)

end proof

end EtcdGrove
end Perennial
