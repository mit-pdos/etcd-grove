/-
Proof of the spec of the same name (the auth plan's S4, 2026-10-24). Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.auth.authStore__UserChangePassword
public import Proof.go_etcd_io.etcd.server.v3.auth.LatestTie
public import Spec.go_etcd_io.etcd.server.v3.auth.authStore__selectPassword
public import Spec.go_etcd_io.etcd.server.v3.auth.authStore__refreshRangePermCache
public import Spec.go_uber_org.zap.Strings
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

theorem auth.authStore.UserChangePassword.wp_tie
    (h_commitRevision : auth.authStore.commitRevision.spec (GF := GF) (hG := hG))
    (h_refresh : auth.authStore.refreshRangePermCache.spec (GF := GF) (hG := hG))
    (h_selectPassword : auth.authStore.selectPassword.spec (GF := GF) (hG := hG))
    (h_String : zap.String.spec (GF := GF) (hG := hG))
    (h_Strings : zap.Strings.spec (GF := GF) (hG := hG))
    (h_Info : zap.Logger.Info.spec (GF := GF) (hG := hG)) :
    auth.authStore.UserChangePassword.specT (GF := GF) (hG := hG) := by
  intro st R M P f T hs Pre Q Post r name b0 sc0
  wp_start as ⟨#Hinv, #Hr, %Hlen, Hown, HWR, Htpa, Hcs, %Hok⟩
  icases authErrVar_of_init .userNotFound $$ Hpkg with ⟨%eUNF, #HeUNF⟩
  icases authErrVar_of_init .noPasswordUser $$ Hpkg with ⟨%eNPU, #HeNPU⟩
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
  iunfold userChangePasswordReqIs at Hr
  icases Hr with ⟨%Hrnn, #HN, ⟨%pw, %hpw, #Hpw, #Hhpw⟩⟩
  iunfold authWRx at HWR
  icases HWR with ⟨⟨%be, Hbe, #Hbeok⟩, HT, Hfl, #Hev, Hca, #Hcsn⟩
  ihave #Hbeok' := Hbeok
  iunfold authWBackendOk at Hbeok'
  icases Hbeok' with ⟨%bi, %Hbi, #HBatch, #HFC, -⟩
  subst Hbi
  wp_apply wp_with_defer as %defer defer
  (try wp_auto)
  wp_apply HBatch as %tx Htx
  iunfold authBatchTxOk at Htx
  icases Htx with ⟨%ti, %Hti, %Lk, #HLk⟩
  subst Hti
  ihave #HLk' := HLk
  iunfold authBatchTxLk at HLk'
  icases HLk' with ⟨#HLock, #HRd, #HPutU, -, -, -, -, -, #HUnlock, -, -⟩
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
    iexists b0, sc0

    isplitl [HA]

    · iunfold tpAdmin; iexists (GoInterface.ok tpi), Atp; iframe HA; iframe #
    isplitl [HPost]
    · ileft; iexact HPost
    isplitl [Hbe HT Hfl Hca]
    · iunfold authWRx; iframe HT Hfl Hev Hca Hcsn; iexists (GoInterface.ok bi); iframe Hbe Hbeok
    isplitr
    · iunfold respOk; isplitr
      · ipureintro; intro _; rfl
      · ileft; ipureintro; rfl
    iunfold adminOutP
    iright
    iexists st0, (.err .userNotFound)
    isplitr
    · ipureintro; exact tieStep_same _ _ _ _
    isplitr
    · ipureintro
      refine ⟨Hl0, ?_⟩
      simp [stepOf, userChangePasswordF, Hnone]
    simp only [outRes, authErrOf, AuthErr.var]
    iframe Hown
    iexists eUNF; iframe HeUNF; ipureintro; rfl
  ihave Hu' := userOut_some _ st0 name Hif $$ Hu
  icases Hu' with ⟨%roles, %ur, %Hur, Hu⟩
  iunfold ownUser at Hu
  icases Hu with ⟨%ums, %unm, %upw, %url, %uo, %uuf, %usc, Hup, #Hunm, #Hupw, #Hurl, #Huo⟩
  icases typedPointsto_split _ _ _ $$ Hup with Hup
  simp only [TypedPointsto.typedPointstoDef]
  iNamed Hup
  ihave %Hpk := authOwnF_last_permKeysOk M hs $$ Hown
  have Hstep := (Hok st0 Hl0)
  (try wp_auto)
  wp_join (Q := fun v => iprop(⌜v = #(decide (uo = null ∨ ur.noPassword = false))⌝ ∗ user_ptr ↦ u ∗
      structFieldRef authpb.User go!"Options" u ↦ uo))
    at (if: _ then #true else _) with [user Options] as ⟨%Hv, user, Options⟩
  · wp_if_destruct
    · iframe; ipureintro; simp
    · iunfold userOptsAt at Huo
      icases Huo with (%Hn | ⟨%Honn, ⟨%oms, %ouf, %osc, #Hom⟩⟩)
      · exact absurd Hn.1 Hif
      icases typedPointsto_split _ _ _ $$ Hom with Homf
      simp only [TypedPointsto.typedPointstoDef]
      iNamed Homf
      (try wp_auto)
      iframe
      ipureintro
      cases ur.noPassword <;> simp [Hif]
  subst Hv
  wp_if_destruct
  · -- the password selected
    (try wp_auto)
    wp_apply (h_selectPassword st pw hpw) as %pwsl %e ⟨%pwb, #Hpwsl, -⟩
    · ipureintro; exact Hst
    (try wp_auto)
    cases e with
    | ok ei =>
      -- no password could be selected: `ErrNoPasswordUser`
      (try wp_auto)
      wp_apply HUnlock $$ %st0 %Post %hs [$HL $Hown] as ⟨HPost, HT, Hown⟩
      · ipureintro; exact Hl0
      (try wp_auto)
      iapply HΦ
      iexists b0, sc0

      isplitl [HA]

      · iunfold tpAdmin; iexists (GoInterface.ok tpi), Atp; iframe HA; iframe #
      isplitl [HPost]
      · ileft; iexact HPost
      isplitl [Hbe HT Hfl Hca]
      · iunfold authWRx; iframe HT Hfl Hev Hca Hcsn; iexists (GoInterface.ok bi); iframe Hbe Hbeok
      isplitr
      · iunfold respOk; isplitr
        · ipureintro; intro _; rfl
        · ileft; ipureintro; rfl
      iunfold adminOutP
      ileft
      iexists .noPasswordUser
      isplitr
      · ipureintro; exact tieStep_same _ _ _ _
      iframe Hown
      isplitr
      · ipureintro; rfl
      simp only [authErrOf, AuthErr.var]
      iexists eNPU; iframe HeNPU; ipureintro; rfl
    | nil =>
      (try wp_auto)
      wp_apply wp_string_to_bytes as %nsl ⟨Hnsl, -⟩
      ipersist Hnsl
      (try wp_auto)
      let urN : UserRec := ⟨name, pwb, ur.roles, ur.noPassword⟩
      ihave Hnu : ownUser «$r0_ptr» urN $$ [«$r0»]
      · iunfold ownUser
        iexists _, _, _, _, _, _, _
        iframe «$r0»
        isplitr
        · iexact Hnsl
        isplitr
        · iexact Hpwsl
        isplitr
        · iexact Hurl
        · iexact Huo
      wp_bind (App (Val #(methods ti.ty go!"UnsafePutUser" ti.v)) (Val #«$r0_ptr»))
      iapply HPutU $$ %st0 %Post %«$r0_ptr» %urN [$HL $Hnu]
      · ipureintro; exact ⟨by rw [Hur.2.1]; exact Hur.2.2, Hlen⟩
      inext
      iintro ⟨HL, -⟩
      have hput : putUser st0 urN.name urN.roles = st0 := by
        simp only [urN, putUser, Hur.2.1]
        cases st0
        simp only [AuthState.mk.injEq, and_true, true_and]
        exact GMap.insert_id _ _ _ Hur.1
      rw [hput]
      (try wp_auto)
      have hstep : userChangePasswordF name st0 = .next (bump st0) := by
        simp [userChangePasswordF, Hur.1]
      obtain ⟨Hrevfit, Hfit⟩ := Hstep
      have Hfit' := Hfit _ _ rfl hstep
      wp_apply (h_commitRevision st R M P f T ti Lk st0 Post hs st0)
        $$ [$Hinv $HLk $HL $Hown] as ⟨%rev, %Hrev, HL, Hown⟩
      · ipureintro
        refine ⟨Hl0, rfl, Hrevfit, fun h1 h2 => Hpk st0 Hl0 h1 h2, ?_⟩
        intro hM; subst hM; exact Hl0
      have Hl1 := histLast_after M hs st0 rev (fun h => by subst h; exact Hl0) Hrev
      imod (authSnapF_of_last M _ _ Hl1) $$ Hown with ⟨Hown, #Hsnap⟩
      (try wp_auto)
      wp_bind (App (Val (st @!! go.GoType.PointerType authStore.ty @!! go!"refreshRangePermCache"))
        (Val #(GoInterface.ok ti)))
      iapply (h_refresh st R M ti (fun x => Lk x Post) ({ st0 with revision := rev } : AuthState) (hs ++ [bump st0]))
        $$ [HL Hca Hown]
      · iframe Hpkg Hinv
        isplitl [Hca]
        · iapply (cacheHalf_of_at _ _ _) $$ Hca Hcsn
        isplitr
        · iapply HRd
        isplitl [HL]
        · iExactEq HL
          all_goals rfl
        iframe Hsnap
        iframe Hown; ipureintro; exact ⟨permsFit_rev _ rev Hfit', fun _ h => by subst h; exact Hl1⟩
      inext
      iintro ⟨HL, Hca, Hown⟩
      (try wp_auto)
      wp_bind (App (Val #(methods tpi.ty go!"invalidateUser" tpi.v)) (Val #name))
      iapply HInval $$ %name [HA] [-]
      · iexact HA
      inext
      iintro HA
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
      wp_apply HUnlock $$ %_ %Post %(hs ++ [bump st0]) [HL $Hown]
        as ⟨HPost, HT, Hown⟩
      · isplitl [HL]
        · iExactEq HL
          all_goals rfl
        ipureintro; exact Hl1
      (try wp_auto)
      iapply HΦ
      iexists b0, ({ st0 with revision := rev } : AuthState)

      isplitl [HA]

      · iunfold tpAdmin; iexists (GoInterface.ok tpi), Atp; iframe HA; iframe #
      isplitl [HPost]
      · ileft; iexact HPost
      isplitl [Hbe HT Hfl Hca]
      · iunfold authWRx; iframe HT Hfl Hev Hca Hsnap; iexists (GoInterface.ok bi); iframe Hbe Hbeok
      isplitl [Header]
      · iunfold respOk; isplitr
        · ipureintro; intro h; exact absurd rfl h
        · iright; iexists _; iexact Header
      iunfold adminOutP
      iright
      iexists st0, (.next (bump st0))
      isplitr
      · ipureintro; exact tieStep_refresh M hs _ b0 sc0 _ st0 Hl0 Hl1 rfl
      isplitr
      · ipureintro; exact ⟨Hl0, hstep.symm⟩
      simp only [outRes]
      iframe Hown
  · -- a no-password user: no password
    (try wp_auto)
    wp_apply wp_string_to_bytes as %nsl ⟨Hnsl, -⟩
    ipersist Hnsl
    (try wp_auto)
    let urN : UserRec := ⟨name, [], ur.roles, ur.noPassword⟩
    ihave Hnu : ownUser «$r0_ptr» urN $$ [«$r0»]
    · iunfold ownUser
      iexists _, _, _, _, _, _, _
      iframe «$r0»
      isplitr
      · iexact Hnsl
      isplitr
      · iapply ownSlice_nil
      isplitr
      · iexact Hurl
      · iexact Huo
    wp_bind (App (Val #(methods ti.ty go!"UnsafePutUser" ti.v)) (Val #«$r0_ptr»))
    iapply HPutU $$ %st0 %Post %«$r0_ptr» %urN [$HL $Hnu]
    · ipureintro; exact ⟨by rw [Hur.2.1]; exact Hur.2.2, Hlen⟩
    inext
    iintro ⟨HL, -⟩
    have hput : putUser st0 urN.name urN.roles = st0 := by
      simp only [urN, putUser, Hur.2.1]
      cases st0
      simp only [AuthState.mk.injEq, and_true, true_and]
      exact GMap.insert_id _ _ _ Hur.1
    rw [hput]
    (try wp_auto)
    have hstep : userChangePasswordF name st0 = .next (bump st0) := by
      simp [userChangePasswordF, Hur.1]
    obtain ⟨Hrevfit, Hfit⟩ := Hstep
    have Hfit' := Hfit _ _ rfl hstep
    wp_apply (h_commitRevision st R M P f T ti Lk st0 Post hs st0)
      $$ [$Hinv $HLk $HL $Hown] as ⟨%rev, %Hrev, HL, Hown⟩
    · ipureintro
      refine ⟨Hl0, rfl, Hrevfit, fun h1 h2 => Hpk st0 Hl0 h1 h2, ?_⟩
      intro hM; subst hM; exact Hl0
    have Hl1 := histLast_after M hs st0 rev (fun h => by subst h; exact Hl0) Hrev
    imod (authSnapF_of_last M _ _ Hl1) $$ Hown with ⟨Hown, #Hsnap⟩
    (try wp_auto)
    wp_bind (App (Val (st @!! go.GoType.PointerType authStore.ty @!! go!"refreshRangePermCache"))
      (Val #(GoInterface.ok ti)))
    iapply (h_refresh st R M ti (fun x => Lk x Post) ({ st0 with revision := rev } : AuthState) (hs ++ [bump st0]))
      $$ [HL Hca Hown]
    · iframe Hpkg Hinv
      isplitl [Hca]
      · iapply (cacheHalf_of_at _ _ _) $$ Hca Hcsn
      isplitr
      · iapply HRd
      isplitl [HL]
      · iExactEq HL
        all_goals rfl
      iframe Hsnap
      iframe Hown; ipureintro; exact ⟨permsFit_rev _ rev Hfit', fun _ h => by subst h; exact Hl1⟩
    inext
    iintro ⟨HL, Hca, Hown⟩
    (try wp_auto)
    wp_bind (App (Val #(methods tpi.ty go!"invalidateUser" tpi.v)) (Val #name))
    iapply HInval $$ %name [HA] [-]
    · iexact HA
    inext
    iintro HA
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
    wp_apply HUnlock $$ %_ %Post %(hs ++ [bump st0]) [HL $Hown]
      as ⟨HPost, HT, Hown⟩
    · isplitl [HL]
      · iExactEq HL
        all_goals rfl
      ipureintro; exact Hl1
    (try wp_auto)
    iapply HΦ
    iexists b0, ({ st0 with revision := rev } : AuthState)

    isplitl [HA]

    · iunfold tpAdmin; iexists (GoInterface.ok tpi), Atp; iframe HA; iframe #
    isplitl [HPost]
    · ileft; iexact HPost
    isplitl [Hbe HT Hfl Hca]
    · iunfold authWRx; iframe HT Hfl Hev Hca Hsnap; iexists (GoInterface.ok bi); iframe Hbe Hbeok
    isplitl [Header]
    · iunfold respOk; isplitr
      · ipureintro; intro h; exact absurd rfl h
      · iright; iexists _; iexact Header
    iunfold adminOutP
    iright
    iexists st0, (.next (bump st0))
    isplitr
    · ipureintro; exact tieStep_refresh M hs _ b0 sc0 _ st0 Hl0 Hl1 rfl
    isplitr
    · ipureintro; exact ⟨Hl0, hstep.symm⟩
    simp only [outRes]
    iframe Hown


theorem auth.authStore.UserChangePassword.wp_proof
    (h_commitRevision : auth.authStore.commitRevision.spec (GF := GF) (hG := hG))
    (h_refresh : auth.authStore.refreshRangePermCache.spec (GF := GF) (hG := hG))
    (h_selectPassword : auth.authStore.selectPassword.spec (GF := GF) (hG := hG))
    (h_String : zap.String.spec (GF := GF) (hG := hG))
    (h_Strings : zap.Strings.spec (GF := GF) (hG := hG))
    (h_Info : zap.Logger.Info.spec (GF := GF) (hG := hG)) :
    auth.authStore.UserChangePassword.spec (GF := GF) (hG := hG) :=
  auth.authStore.UserChangePassword.spec_of_T (auth.authStore.UserChangePassword.wp_tie h_commitRevision h_refresh h_selectPassword h_String h_Strings h_Info)

end proof

end EtcdGrove
end Perennial
