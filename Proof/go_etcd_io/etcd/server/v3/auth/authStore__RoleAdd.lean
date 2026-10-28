/-
Proof of the spec of the same name (the auth plan's S4, 2026-10-24). Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.auth.authStore__RoleAdd
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

theorem auth.authStore.RoleAdd.wp_tieB
    (h_commitRevision : auth.authStore.commitRevision.spec (GF := GF) (hG := hG))
    (h_String : zap.String.spec (GF := GF) (hG := hG))
    (h_Info : zap.Logger.Info.spec (GF := GF) (hG := hG)) :
    auth.authStore.RoleAdd.specTB (GF := GF) (hG := hG) := by
  intro st R M P f T hs Pre Q Post r name b0 sc0 be
  wp_start as ⟨#Hinv, #Hr, %Hlen, Hown, HWR, Hcs, %Hok⟩
  icases authErrVar_of_init .roleEmpty $$ Hpkg with ⟨%eRE, #HeRE⟩
  icases authErrVar_of_init .roleAlreadyExist $$ Hpkg with ⟨%eRAE, #HeRAE⟩
  simp only [AuthErr.var]
  ihave #Hinv' := Hinv
  iunfold authInv at Hinv'
  icases Hinv' with ⟨%Hst, -, ⟨%lg, #Hlg, %Hlgnn⟩, -, -, -, -⟩
  iunfold roleAddReqIs at Hr
  icases Hr with ⟨%Hrnn, #HN⟩
  iunfold authWRxB at HWR
  icases HWR with ⟨⟨Hbe, #Hbeok⟩, HT, Hfl, #Hev, Hca, #Hcsn⟩
  ihave #Hbeok' := Hbeok
  iunfold authWBackendOk at Hbeok'
  icases Hbeok' with ⟨%bi, %Hbi, #HBatch, #HFC, -⟩
  subst Hbi
  wp_auto
  wp_apply wp_with_defer as %defer defer
  (try wp_auto)
  wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len as %Hnl
  wp_if_destruct
  · -- an empty name
    (try wp_auto)
    iapply HΦ
    iexists b0, sc0
    isplitl [Hcs]
    · iapply csContract_noWrite $$ Hcs
    isplitl [Hbe HT Hfl Hca]
    · iunfold authWRxB; iframe HT Hfl Hev Hca Hcsn; iframe Hbe Hbeok
    isplitr
    · iunfold respOk; isplitr
      · ipureintro; intro _; rfl
      · ileft; ipureintro; rfl
    iunfold adminOutP
    iright
    ihave %Hl := authOwn_exists_last M hs $$ Hown
    obtain ⟨st0, Hl⟩ := Hl
    iexists st0, (.err .roleEmpty)
    isplitr
    · ipureintro; exact tieStep_same _ _ _ _
    isplitr
    · ipureintro
      refine ⟨Hl, ?_⟩
      have : name = [] := by
        cases name with
        | nil => rfl
        | cons a l =>
          exfalso
          have h1 : l.length + 1 < 2 ^ 63 := by simpa using Hnl
          simp only [List.length_cons] at Hif
          word
      simp [stepOf, roleAddF, this]
    simp only [outRes]
    iframe Hown
    simp only [authErrOf, AuthErr.var]; iexists eRE; iframe HeRE; ipureintro; rfl
  have hname : name ≠ [] := by
    intro h; subst h; simp at Hif
  clear Hif
  wp_apply HBatch as %tx Htx
  iunfold authBatchTxOk at Htx
  icases Htx with ⟨%ti, %Hti, %Lk, #HLk⟩
  subst Hti
  ihave #HLk' := HLk
  iunfold authBatchTxLk at HLk'
  icases HLk' with ⟨#HLock, #HRd, -, -, #HPutR, -, -, -, #HUnlock, -, -⟩
  (try wp_auto)
  wp_bind (App (Val #(methods ti.ty go!"Lock" ti.v)) (Val #()))
  iapply HLock $$ %hs %Pre %Q %Post [$Hcs $HT $Hown]
  inext
  iintro ⟨%st0, HL, Hown, %Hl0⟩
  ihave #HRd' := HRd $$ %Post
  iunfold authReaderOk at HRd'
  icases HRd' with ⟨-, #HUGR, -, -, -⟩
  (try wp_auto)
  wp_bind (App (Val #(methods ti.ty go!"UnsafeGetRole" ti.v)) (Val #name))
  iapply HUGR $$ %st0 %name HL
  inext
  iintro %rl ⟨HL, Hrl⟩
  (try wp_auto)
  wp_if_destruct
  rotate_left
  · -- an existing role
    ihave Hrl' := roleOut_some _ st0 name Hif $$ Hrl
    icases Hrl' with ⟨%ps, %rr, %Hrr, -⟩
    wp_apply HUnlock $$ %st0 %Post %hs [$HL $Hown] as ⟨HPost, HT, Hown⟩
    · ipureintro; exact Hl0
    (try wp_auto)
    iapply HΦ
    iexists b0, sc0
    isplitl [HPost]
    · ileft; iexact HPost
    isplitl [Hbe HT Hfl Hca]
    · iunfold authWRxB; iframe HT Hfl Hev Hca Hcsn; iframe Hbe Hbeok
    isplitr
    · iunfold respOk; isplitr
      · ipureintro; intro _; rfl
      · ileft; ipureintro; rfl
    iunfold adminOutP
    iright
    iexists st0, (.err .roleAlreadyExist)
    isplitr
    · ipureintro; exact tieStep_same _ _ _ _
    isplitr
    · ipureintro
      refine ⟨Hl0, ?_⟩
      simp [stepOf, roleAddF, hname, Hrr.1]
    simp only [outRes, authErrOf, AuthErr.var]
    iframe Hown
    iexists eRAE; iframe HeRAE; ipureintro; rfl
  ihave %Hnone := roleOut_null st0 name $$ Hrl
  ihave %Hpk := authOwnF_last_permKeysOk M hs $$ Hown
  have Hstep := (Hok st0 Hl0)
  wp_apply wp_string_to_bytes as %nsl ⟨Hnsl, -⟩
  ipersist Hnsl
  (try wp_auto)
  let rrN : RoleRec := ⟨name, []⟩
  ihave Hnr : ownRole «$r0_ptr» rrN $$ [«$r0»]
  · iunfold ownRole
    iexists _, _, _, [], _, _
    iframe «$r0»
    isplitr
    · iexact Hnsl
    isplitr
    · iapply ownSlice_nil
    isplitr
    · ipureintro; rfl
    · simp only [List.zip_nil_left]; iapply BigSepL.bigSepL_nil.2; itrivial
  wp_bind (App (Val #(methods ti.ty go!"UnsafePutRole" ti.v)) (Val #«$r0_ptr»))
  iapply HPutR $$ %st0 %Post %«$r0_ptr» %rrN %rrN.toRole [$HL $Hnr]
  · ipureintro; exact ⟨Hlen, List.Perm.refl _⟩
  inext
  iintro ⟨HL, -⟩
  (try wp_auto)
  have hstep : roleAddF name st0 = .next (bump (putRole st0 name [])) := by
    simp [roleAddF, hname, Hnone]
  obtain ⟨Hrevfit, Hfit⟩ := Hstep
  wp_apply (h_commitRevision st R M P f T ti Lk (putRole st0 rrN.name rrN.toRole) Post hs st0)
    $$ [$Hinv $HLk $HL $Hown] as ⟨%rev, %Hrev, HL, Hown⟩
  · ipureintro
    refine ⟨Hl0, rfl, Hrevfit, fun h1 h2 => permKeysOk_putRole _ _ _ (Hpk st0 Hl0 h1 h2) (by simp [rrN, RoleRec.toRole]), ?_⟩
    intro hM; subst hM; exact Hl0
  have Hl1 := histLast_after M hs (putRole st0 rrN.name rrN.toRole) rev (fun h => by subst h; exact Hl0) Hrev
  (try wp_auto)
  wp_apply h_String _ _ as %f1 -
  (try wp_auto)
  wp_apply wp_slice_literal (V := go_uber_org.zap.zapcore.Field) [f1]
  isplitr
  · ipureintro; rfl
  iintro %fsl ⟨-, -⟩
  (try wp_auto)
  wp_apply h_Info
  · ipureintro; exact Hlgnn
  (try wp_auto)
  irename «$r0» => Hresp
  generalize «$r0_ptr» = resp at *
  icases typedPointsto_split _ _ _ $$ Hresp with Hresp
  simp only [TypedPointsto.typedPointstoDef]
  iNamed Hresp
  (try wp_auto)
  wp_apply HUnlock $$ %_ %Post %(hs ++ [bump (putRole st0 rrN.name rrN.toRole)]) [HL $Hown]
    as ⟨HPost, HT, Hown⟩
  · isplitl [HL]
    · iExactEq HL; rfl
    ipureintro; exact Hl1
  (try wp_auto)
  by_cases hc : b0 = true ∧ sc0 = st0
  · ihave Hca := cacheAt_congr st M sc0 ({ putRole st0 rrN.name rrN.toRole with revision := rev })
      (by rw [hc.2]; rfl) (fun u => by
        rw [hc.2]; exact (userPerms_putRole_empty st0 name Hnone u).symm) $$ Hca
    ihave ⟨Hown, #Hsn'⟩ := authSnap_of_own_last M _ _ Hl1 $$ Hown
    iapply HΦ
    iexists b0, ({ putRole st0 rrN.name rrN.toRole with revision := rev } : AuthState)
    isplitl [HPost]
    · ileft; iexact HPost
    isplitl [Hbe HT Hfl Hca]
    · iunfold authWRxB; iframe HT Hfl Hev Hca Hsn'; iframe Hbe Hbeok
    isplitl [Header]
    · iunfold respOk; isplitr
      · ipureintro; intro h; exact absurd rfl h
      · iright; iexists _; iexact Header
    iunfold adminOutP
    iright
    iexists st0, (.next (bump (putRole st0 name [])))
    isplitr
    · ipureintro; exact tieStep_refresh M hs _ b0 sc0 _ st0 Hl0 Hl1 rfl
    isplitr
    · ipureintro; exact ⟨Hl0, hstep.symm⟩
    simp only [outRes]
    isplitl [Hown]
    · iExactEq Hown
      all_goals rfl
    · ipureintro; trivial
  · iapply HΦ
    iexists b0, sc0
    isplitl [HPost]
    · ileft; iexact HPost
    isplitl [Hbe HT Hfl Hca]
    · iunfold authWRxB; iframe HT Hfl Hev Hca Hcsn; iframe Hbe Hbeok
    isplitl [Header]
    · iunfold respOk; isplitr
      · ipureintro; intro h; exact absurd rfl h
      · iright; iexists _; iexact Header
    iunfold adminOutP
    iright
    iexists st0, (.next (bump (putRole st0 name [])))
    isplitr
    · ipureintro; exact tieStep_keep' M hs _ b0 sc0 st0 _ Hl0 Hl1 rfl (permView_putRole_empty st0 name Hnone) hc
    isplitr
    · ipureintro; exact ⟨Hl0, hstep.symm⟩
    simp only [outRes]
    isplitl [Hown]
    · iExactEq Hown
      all_goals rfl
    · ipureintro; trivial


theorem auth.authStore.RoleAdd.wp_tie
    (h_commitRevision : auth.authStore.commitRevision.spec (GF := GF) (hG := hG))
    (h_String : zap.String.spec (GF := GF) (hG := hG))
    (h_Info : zap.Logger.Info.spec (GF := GF) (hG := hG)) :
    auth.authStore.RoleAdd.specT (GF := GF) (hG := hG) :=
  auth.authStore.RoleAdd.specT_of_TB (auth.authStore.RoleAdd.wp_tieB h_commitRevision h_String h_Info)

theorem auth.authStore.RoleAdd.wp_proof
    (h_commitRevision : auth.authStore.commitRevision.spec (GF := GF) (hG := hG))
    (h_String : zap.String.spec (GF := GF) (hG := hG))
    (h_Info : zap.Logger.Info.spec (GF := GF) (hG := hG)) :
    auth.authStore.RoleAdd.spec (GF := GF) (hG := hG) :=
  auth.authStore.RoleAdd.spec_of_T (auth.authStore.RoleAdd.wp_tie h_commitRevision h_String h_Info)

end proof

end EtcdGrove
end Perennial
