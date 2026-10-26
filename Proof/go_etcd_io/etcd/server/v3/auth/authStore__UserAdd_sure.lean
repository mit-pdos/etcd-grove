/-
`UserAdd.specSure` (the auth plan's E2u, 2026-10-26): `UserAdd` of a request whose password choice
cannot fail (`userAddSure`: no password, or an empty `Password` with a base64-encoded
`HashedPassword`) never returns `ErrNoPasswordUser`, so its outcome is the step's alone
(`noExtra`). The proof is `UserAdd.wp_proof`'s, with the error branch of `selectPassword` ruled out
by its boundary spec. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.auth.authStore__UserAdd
public import Proof.go_etcd_io.etcd.server.v3.auth.VerdictLemmas
public import Spec.go_etcd_io.etcd.server.v3.auth.authStore__commitRevision
public import Spec.go_etcd_io.etcd.server.v3.auth.authStore__refreshRangePermCache
public import Spec.go_etcd_io.etcd.server.v3.auth.authStore__selectPassword
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

/-- Two persistent views of one options field agree on `NoPassword`. -/
theorem userOptsAt_agree (o : Loc) (b1 b2 : Bool) :
    userOptsAt (GF := GF) o b1 ⊢ userOptsAt o b2 -∗ ⌜b1 = b2⌝ := by
  iunfold userOptsAt
  iintro H1 H2
  icases H1 with (%H1 | ⟨%Hnn1, %ms1, %uf1, %sc1, H1⟩)
  · icases H2 with (%H2 | ⟨%Hnn2, -⟩)
    · ipureintro; rw [H1.2, H2.2]
    · exact absurd H1.1 Hnn2
  · icases H2 with (%H2 | ⟨%Hnn2, %ms2, %uf2, %sc2, H2⟩)
    · exact absurd H2.1 Hnn1
    · icombine H1 H2 gives %h
      ipureintro
      injection h

theorem auth.authStore.UserAdd.wp_sure
    (h_commitRevision : auth.authStore.commitRevision.spec (GF := GF) (hG := hG))
    (h_refresh : auth.authStore.refreshRangePermCache.spec (GF := GF) (hG := hG))
    (h_selectPassword : auth.authStore.selectPassword.spec (GF := GF) (hG := hG))
    (h_String : zap.String.spec (GF := GF) (hG := hG))
    (h_Info : zap.Logger.Info.spec (GF := GF) (hG := hG)) :
    auth.authStore.UserAdd.specSure (GF := GF) (hG := hG) := by
  intro st R M P f T hs Pre Q Post r name
  wp_start as ⟨#Hinv, #Hr, #Hsure, %Hlen, Hown, HWR, Hcs, %Hok⟩
  icases authErrVar_of_init .userEmpty $$ Hpkg with ⟨%eUE, #HeUE⟩
  icases authErrVar_of_init .userAlreadyExist $$ Hpkg with ⟨%eUAE, #HeUAE⟩
  icases authErrVar_of_init .noPasswordUser $$ Hpkg with ⟨%eNPU, #HeNPU⟩
  simp only [AuthErr.var]
  ihave #Hinv' := Hinv
  iunfold authInv at Hinv'
  icases Hinv' with ⟨%Hst, -, ⟨%lg, #Hlg, %Hlgnn⟩, -, -, -, -⟩
  iunfold userAddReqIs at Hr
  icases Hr with ⟨%Hrnn, #HN, ⟨%pw, %hpw, #Hpw, #Hhpw⟩, ⟨%o, %nob, #Ho, #Hopts⟩⟩
  iunfold authWR at HWR
  icases HWR with ⟨⟨%be, Hbe, #Hbeok⟩, HT, Hen, Hca⟩
  ihave #Hbeok' := Hbeok
  iunfold authWBackendOk at Hbeok'
  icases Hbeok' with ⟨%bi, %Hbi, #HBatch, #HFC, -⟩
  subst Hbi
  wp_apply wp_with_defer as %defer defer
  (try wp_auto)
  wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len as %Hnl
  wp_if_destruct
  · -- an empty name
    (try wp_auto)
    iapply HΦ
    isplitl [Hcs]
    · iapply csContract_noWrite $$ Hcs
    isplitl [Hbe HT Hen Hca]
    · iunfold authWR; iframe HT Hen Hca; iexists (GoInterface.ok bi); iframe Hbe Hbeok
    isplitr
    · iunfold respOk; isplitr
      · ipureintro; intro _; rfl
      · ileft; ipureintro; rfl
    iunfold adminOut
    iright
    ihave %Hl := authOwn_exists_last M hs $$ Hown
    obtain ⟨st0, Hl⟩ := Hl
    iexists st0, (.err .userEmpty)
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
      simp [stepOf, userAddF, this]
    simp only [outRes]
    iframe Hown
    simp only [authErrOf, AuthErr.var]; iexists eUE; iframe HeUE; ipureintro; rfl
  have hname : name ≠ [] := by
    intro h; subst h; simp at Hif
  clear Hif
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
  icases HRd' with ⟨#HUG, -, #HRE, #HRR, -⟩
  (try wp_auto)
  wp_bind (App (Val #(methods ti.ty go!"UnsafeGetUser" ti.v)) (Val #name))
  iapply HUG $$ %st0 %name HL
  inext
  iintro %u ⟨HL, Hu⟩
  (try wp_auto)
  wp_if_destruct
  rotate_left
  · -- an existing user
    ihave Hu' := userOut_some _ st0 name Hif $$ Hu
    icases Hu' with ⟨%roles, %ur, %Hur, -⟩
    wp_apply HUnlock $$ %st0 %Post %hs [$HL $Hown] as ⟨HPost, HT, Hown⟩
    · ipureintro; exact Hl0
    (try wp_auto)
    iapply HΦ
    isplitl [HPost]
    · ileft; iexact HPost
    isplitl [Hbe HT Hen Hca]
    · iunfold authWR; iframe HT Hen Hca; iexists (GoInterface.ok bi); iframe Hbe Hbeok
    isplitr
    · iunfold respOk; isplitr
      · ipureintro; intro _; rfl
      · ileft; ipureintro; rfl
    iunfold adminOut
    iright
    iexists st0, (.err .userAlreadyExist)
    isplitr
    · ipureintro
      refine ⟨Hl0, ?_⟩
      simp [stepOf, userAddF, hname, Hur.1]
    simp only [outRes, authErrOf, AuthErr.var]
    iframe Hown
    iexists eUAE; iframe HeUAE; ipureintro; rfl
  ihave %Hnone := userOut_null st0 name $$ Hu
  wp_join iprop(∃ (o' : Loc) (b : Bool) (ms : google_golang_org.protobuf.internal.impl.MessageState)
      (uf : GoSlice) (sc : w32) (dq : DFrac), options_ptr ↦ o' ∗ ⌜o' ≠ null⌝ ∗
      o' ↦{dq} ({ state' := ms, NoPassword' := b, unknownFields' := uf, sizeCache' := sc } :
        authpb.UserAddOptions) ∗ ⌜b = nob⌝)
    with [options] as ⟨%o', %b, %ms, %uf, %sc, %dq, options, %Ho'nn, Hom, %Hbnob⟩
  · -- nil options: `&authpb.UserAddOptions{NoPassword: false}`
    ihave %Hpnn := typedPointsto_not_null _ _ _ $$ «$r0»
    iexists «$r0_ptr», false, _, _, _, _
    iframe options «$r0»
    iunfold userOptsAt at Hopts
    icases Hopts with (%Hn | ⟨%Honn, -⟩)
    · ipureintro; exact ⟨Hpnn, Hn.2.symm⟩
    · exact absurd rfl Honn
  · -- the request's options
    iunfold userOptsAt at Hopts
    icases Hopts with (%Hn | ⟨%Honn, ⟨%ms, %uf, %sc, Hm⟩⟩)
    · exact absurd Hn.1 Hif
    iexists o, nob, ms, uf, sc, DFrac.discard
    iframe options Hm
    ipureintro; exact ⟨Honn, rfl⟩
  ipersist Hom
  ihave #Hopts' : userOptsAt o' b $$ []
  · iunfold userOptsAt; iright; isplitr
    · ipureintro; exact Ho'nn
    iexists ms, uf, sc; iexact Hom
  ihave Homf := typedPointsto_split _ _ _ $$ Hom
  simp only [TypedPointsto.typedPointstoDef]
  iNamed Homf
  (try wp_auto)
  cases b
  · -- the password selected
    (try wp_auto)
    wp_apply (h_selectPassword st pw hpw) as %pwsl %e ⟨%pwb, #Hpwsl, %Hsel⟩
    · ipureintro; exact Hst
    (try wp_auto)
    cases e with
    | ok ei =>
      -- impossible: the password choice cannot fail (`userAddSure`)
      iunfold userAddSure at Hsure
      icases Hsure with ⟨%pw2, %hpw2, %o2, %b2, #Hpw2, #Hhpw2, #Ho2, #Hb2, %Hsp⟩
      icombine Hpw Hpw2 gives %Epw
      icombine Hhpw Hhpw2 gives %Ehpw
      icombine Ho Ho2 gives %Eo
      subst Epw Ehpw Eo
      ihave %Eb := userOptsAt_agree o nob b2 $$ Hopts Hb2
      subst Eb
      rcases Hsp with Hnb | ⟨Hp, Hx⟩
      · simp_all
      · exact absurd (Hsel Hp Hx) (by simp)
    | nil =>
      (try wp_auto)
      ihave %Hpk := authOwnF_last_permKeysOk M hs $$ Hown
      have Hstep := (Hok st0 Hl0)
      wp_apply wp_string_to_bytes as %nsl ⟨Hnsl, -⟩
      ipersist Hnsl
      (try wp_auto)
      let urN : UserRec := ⟨name, pwb, [], false⟩
      ihave Hnu : ownUser «$r0_ptr» urN $$ [«$r0»]
      · iunfold ownUser
        iexists _, _, _, _, _, _, _
        iframe «$r0»
        isplitr
        · iexact Hnsl
        isplitr
        · iexact Hpwsl
        isplitr
        · iapply ownSlice_nil
        · iexact Hopts'
      wp_bind (App (Val #(methods ti.ty go!"UnsafePutUser" ti.v)) (Val #«$r0_ptr»))
      iapply HPutU $$ %st0 %Post %«$r0_ptr» %urN [$HL $Hnu]
      · ipureintro; exact ⟨List.Pairwise.nil, Hlen⟩
      inext
      iintro ⟨HL, -⟩
      (try wp_auto)
      have hstep : userAddF name st0 = .next (bump (putUser st0 name [])) := by
        simp [userAddF, hname, Hnone]
      obtain ⟨Hrevfit, Hfit⟩ := Hstep
      have Hfit' := Hfit _ _ rfl hstep
      wp_apply (h_commitRevision st R M P f T ti Lk (putUser st0 urN.name urN.roles) Post hs st0)
        $$ [$Hinv $HLk $HL $Hown] as ⟨%rev, %Hrev, HL, Hown⟩
      · ipureintro
        refine ⟨Hl0, rfl, Hrevfit, fun h1 h2 => permKeysOk_putUser _ _ _ (Hpk st0 Hl0 h1 h2), ?_⟩
        intro hM; subst hM; exact Hl0
      have Hl1 := histLast_after M hs (putUser st0 urN.name urN.roles) rev (fun h => by subst h; exact Hl0) Hrev
      imod (authSnapF_of_last M _ _ Hl1) $$ Hown with ⟨Hown, #Hsnap⟩
      wp_bind (App (Val (st @!! go.GoType.PointerType authStore.ty @!! go!"refreshRangePermCache"))
        (Val #(GoInterface.ok ti)))
      iapply (h_refresh st R M ti (fun x => Lk x Post) ({ putUser st0 urN.name urN.roles with revision := rev } : AuthState) (hs ++ [bump (putUser st0 urN.name urN.roles)]))
        $$ [HL Hca Hown]
      · iframe Hpkg Hinv Hca
        isplitr
        · iapply HRd
        isplitl [HL]
        · iExactEq HL; rfl
        iframe Hsnap
        iframe Hown; ipureintro; exact ⟨permsFit_rev _ rev Hfit', fun _ h => by subst h; exact Hl1⟩
      inext
      iintro ⟨HL, Hca, Hown⟩
      ihave Hca := cacheHalf_of_at _ _ _ $$ Hca Hsnap
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
      wp_alloc resp as Hresp
      ihave %Hrespnn := typedPointsto_not_null _ _ _ $$ Hresp
      icases typedPointsto_split _ _ _ $$ Hresp with Hresp
      simp only [TypedPointsto.typedPointstoDef]
      iNamed Hresp
      (try wp_auto)
      wp_apply HUnlock $$ %_ %Post %(hs ++ [bump (putUser st0 urN.name urN.roles)]) [HL $Hown]
        as ⟨HPost, HT, Hown⟩
      · isplitl [HL]
        · iExactEq HL; rfl
        ipureintro; exact Hl1
      (try wp_auto)
      iapply HΦ
      isplitl [HPost]
      · ileft; iexact HPost
      isplitl [Hbe HT Hen Hca]
      · iunfold authWR; iframe HT Hen Hca; iexists (GoInterface.ok bi); iframe Hbe Hbeok
      isplitl [Header]
      · iunfold respOk; isplitr
        · ipureintro; intro h; exact absurd rfl h
        · iright; iexists _; iexact Header
      iunfold adminOut
      iright
      iexists st0, (.next (bump (putUser st0 name [])))
      isplitr
      · ipureintro; exact ⟨Hl0, hstep.symm⟩
      simp only [outRes]
      iframe Hown
  · -- a no-password user: none
    (try wp_auto)
    ihave %Hpk := authOwnF_last_permKeysOk M hs $$ Hown
    have Hstep := (Hok st0 Hl0)
    wp_apply wp_string_to_bytes as %nsl ⟨Hnsl, -⟩
    ipersist Hnsl
    (try wp_auto)
    let urN : UserRec := ⟨name, [], [], true⟩
    ihave Hnu : ownUser «$r0_ptr» urN $$ [«$r0»]
    · iunfold ownUser
      iexists _, _, _, _, _, _, _
      iframe «$r0»
      isplitr
      · iexact Hnsl
      isplitr
      · iapply ownSlice_nil
      isplitr
      · iapply ownSlice_nil
      · iexact Hopts'
    wp_bind (App (Val #(methods ti.ty go!"UnsafePutUser" ti.v)) (Val #«$r0_ptr»))
    iapply HPutU $$ %st0 %Post %«$r0_ptr» %urN [$HL $Hnu]
    · ipureintro; exact ⟨List.Pairwise.nil, Hlen⟩
    inext
    iintro ⟨HL, -⟩
    (try wp_auto)
    have hstep : userAddF name st0 = .next (bump (putUser st0 name [])) := by
      simp [userAddF, hname, Hnone]
    obtain ⟨Hrevfit, Hfit⟩ := Hstep
    have Hfit' := Hfit _ _ rfl hstep
    wp_apply (h_commitRevision st R M P f T ti Lk (putUser st0 urN.name urN.roles) Post hs st0)
      $$ [$Hinv $HLk $HL $Hown] as ⟨%rev, %Hrev, HL, Hown⟩
    · ipureintro
      refine ⟨Hl0, rfl, Hrevfit, fun h1 h2 => permKeysOk_putUser _ _ _ (Hpk st0 Hl0 h1 h2), ?_⟩
      intro hM; subst hM; exact Hl0
    have Hl1 := histLast_after M hs (putUser st0 urN.name urN.roles) rev (fun h => by subst h; exact Hl0) Hrev
    imod (authSnapF_of_last M _ _ Hl1) $$ Hown with ⟨Hown, #Hsnap⟩
    wp_bind (App (Val (st @!! go.GoType.PointerType authStore.ty @!! go!"refreshRangePermCache"))
      (Val #(GoInterface.ok ti)))
    iapply (h_refresh st R M ti (fun x => Lk x Post) ({ putUser st0 urN.name urN.roles with revision := rev } : AuthState) (hs ++ [bump (putUser st0 urN.name urN.roles)]))
      $$ [HL Hca Hown]
    · iframe Hpkg Hinv Hca
      isplitr
      · iapply HRd
      isplitl [HL]
      · iExactEq HL; rfl
      iframe Hsnap
      iframe Hown; ipureintro; exact ⟨permsFit_rev _ rev Hfit', fun _ h => by subst h; exact Hl1⟩
    inext
    iintro ⟨HL, Hca, Hown⟩
    ihave Hca := cacheHalf_of_at _ _ _ $$ Hca Hsnap
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
    wp_alloc resp as Hresp
    ihave %Hrespnn := typedPointsto_not_null _ _ _ $$ Hresp
    icases typedPointsto_split _ _ _ $$ Hresp with Hresp
    simp only [TypedPointsto.typedPointstoDef]
    iNamed Hresp
    (try wp_auto)
    wp_apply HUnlock $$ %_ %Post %(hs ++ [bump (putUser st0 urN.name urN.roles)]) [HL $Hown]
      as ⟨HPost, HT, Hown⟩
    · isplitl [HL]
      · iExactEq HL; rfl
      ipureintro; exact Hl1
    (try wp_auto)
    iapply HΦ
    isplitl [HPost]
    · ileft; iexact HPost
    isplitl [Hbe HT Hen Hca]
    · iunfold authWR; iframe HT Hen Hca; iexists (GoInterface.ok bi); iframe Hbe Hbeok
    isplitl [Header]
    · iunfold respOk; isplitr
      · ipureintro; intro h; exact absurd rfl h
      · iright; iexists _; iexact Header
    iunfold adminOut
    iright
    iexists st0, (.next (bump (putUser st0 name [])))
    isplitr
    · ipureintro; exact ⟨Hl0, hstep.symm⟩
    simp only [outRes]
    iframe Hown

end proof

end EtcdGrove
end Perennial
