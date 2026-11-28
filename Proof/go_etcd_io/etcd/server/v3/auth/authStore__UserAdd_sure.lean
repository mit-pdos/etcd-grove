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
public import Proof.ReceiptTactics

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.auth auth go_etcd_io.etcd.api.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.auth.Assumptions]

/-- Two persistent views of one options field agree on `NoPassword`. -/
theorem userOptsAt_agree (o : Loc) (b1 b2 : Bool) :
    userOptsAt (GF := GF) o b1 ⊢ userOptsAt o b2 -∗ ⌜b1 = b2⌝ := by
  iunfold userOptsAt
  iintro ⟨%ou1, -, H1⟩ ⟨%ou2, -, H2⟩
  iunfold userOptsIs at H1
  iunfold userOptsIs at H2
  icases H1 with (%H1 | ⟨%Hnn1, %uf1, %u1, -, H1, -, -, -⟩)
  · icases H2 with (%H2 | ⟨%Hnn2, -⟩)
    · ipureintro; rw [H1.2.1, H2.2.1]
    · exact absurd H1.1 Hnn2
  · icases H2 with (%H2 | ⟨%Hnn2, %uf2, %u2, -, H2, -, -, -⟩)
    · exact absurd H2.1 Hnn1
    · icombine H1 H2 gives %h
      ipureintro
      first | exact h | exact h.2 | simpa using h

theorem auth.authStore.UserAdd.wp_sure
    (h_commitRevision : auth.authStore.commitRevision.spec (GF := GF) (hG := hG))
    (h_refresh : auth.authStore.refreshRangePermCache.spec (GF := GF) (hG := hG))
    (h_selectPassword : auth.authStore.selectPassword.spec (GF := GF) (hG := hG))
    (h_String : zap.String.spec (GF := GF) (hG := hG))
    (h_Info : zap.Logger.Info.spec (GF := GF) (hG := hG)) :
    auth.authStore.UserAdd.specSure (GF := GF) (hG := hG) := by
  intro st R M P f T Wb hs Pre Q Post r name nob
  wp_start as ⟨#Hinv, #Hr, #Hsure, %Hlen, Hown, HWR, Hw1, Hw2, Hcs, %Hok, #Hcap⟩
  icases authErrVar_of_init .userEmpty $$ Hpkg with ⟨%eUE, #HeUE⟩
  icases authErrVar_of_init .userAlreadyExist $$ Hpkg with ⟨%eUAE, #HeUAE⟩
  icases authErrVar_of_init .noPasswordUser $$ Hpkg with ⟨%eNPU, #HeNPU⟩
  simp only [AuthErr.var]
  ihave #Hinv' := Hinv
  iunfold authInv at Hinv'
  icases Hinv' with ⟨%Hst, -, ⟨%lg, #Hlg, #Hlgnn⟩, -, -, -, -⟩
  iunfold userAddReqIs at Hr
  icases Hr with ⟨%Hrnn, #HN, ⟨%pw, %hpw, #Hpw, #Hhpw⟩, ⟨%o, #Ho, #Hopts⟩⟩
  iunfold authWR at HWR
  icases HWR with ⟨⟨%be, Hbe, #Hbeok⟩, HT, Hen, Hca⟩
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
    isplitl [Hcs]
    · iapply csContract_noWrite $$ Hcs
    isplitl [Hbe HT Hen Hca]
    · iunfold authWR; iframe HT Hen Hca; iexists (GoInterface.ok bi); iframe Hbe Hbeok
    isplitr
    · iunfold respOk; isplitr
      · ipureintro; exact ⟨fun _ => rfl, fun h => by cases h⟩
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
  icases Htx with ⟨%ti, %Hti, %Lk, %Sw, #HLk⟩
  subst Hti
  ihave #HLk' := HLk
  iunfold authBatchTxLk at HLk'
  icases HLk' with ⟨#HLock, #HRd, #HPutU, -, -, -, -, -, #HUnlock, -, -⟩
  (try wp_auto)
  wp_bind (App (Val #(methods ti.ty go!"Lock" ti.v)) (Val #()))
  iapply HLock $$ %hs %Pre %Q %Post [$Hcs $HT $Hown]
  inext
  iintro ⟨%st0, HL, Hsw, Hown, %Hl0⟩
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
    wp_apply HUnlock $$ %st0 %Post %hs [$HL $Hsw $Hown $Hw1 $Hw2] as ⟨HPost, HT, Hown⟩
    · ipureintro; exact Hl0
    (try wp_auto)
    iapply HΦ
    isplitl [HPost]
    · ileft; iexact HPost
    isplitl [Hbe HT Hen Hca]
    · iunfold authWR; iframe HT Hen Hca; iexists (GoInterface.ok bi); iframe Hbe Hbeok
    isplitr
    · iunfold respOk; isplitr
      · ipureintro; exact ⟨fun _ => rfl, fun h => by cases h⟩
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
  -- the fresh `Options`' size cache goes into its invariant: `R` under an update
  wp_join iprop(|={⊤}=> ∃ (o' : Loc) (b : Bool) (ou : Option GoString), options_ptr ↦ o' ∗
      ⌜o' ≠ null ∧ userOptsUfOk ou⌝ ∗ userOptsIs o' b ou ∗ ⌜b = nob⌝)
    with [options]
  · -- nil options: `&authpb.UserAddOptions{NoPassword: false}`
    ihave %Hpnn := typedPointsto_not_null _ _ _ $$ «$r0»
    imod userOptsIs_freeze ⊤ «$r0_ptr» _ false _ [] _ $$ [«$r0»] with #Hfo
    · iframe «$r0»; iapply ownSlice_nil
    imodintro
    iexists «$r0_ptr», false, some []
    iframe options Hfo
    isplitr
    · ipureintro; exact ⟨Hpnn, userOptsUfOk_empty⟩
    iunfold userOptsAt at Hopts
    icases Hopts with ⟨%ou, -, Hopts⟩
    iunfold userOptsIs at Hopts
    icases Hopts with (%Hn | ⟨%Honn, -⟩)
    · ipureintro; exact Hn.2.1.symm
    · exact absurd rfl Honn
  · -- the request's options
    iunfold userOptsAt at Hopts
    icases Hopts with ⟨%ou, %Hou, #Hopts⟩
    ihave #Hopts2 := Hopts
    iunfold userOptsIs at Hopts2
    icases Hopts2 with (%Hn | ⟨%Honn, -⟩)
    · exact absurd Hn.1 Hif
    imodintro
    iexists o, nob, ou
    iframe options Hopts
    ipureintro; exact ⟨⟨Honn, Hou⟩, rfl⟩
  iintro HR
  imod HR with ⟨%o', %b, %ou, options, %Ho'nn, #Hopts', %Hbnob⟩
  (try wp_auto)
  ihave #Hom := Hopts'
  iunfold userOptsIs at Hom
  icases Hom with (%Hn | ⟨-, %uf, %u, -, #NoPassword, -, -, -⟩)
  · exact absurd Hn.1 Ho'nn.1
  (try wp_auto)
  cases b
  · -- the password selected
    (try wp_auto)
    ihave #Hbc := auth.authInv_bcryptCost _ _ _ $$ Hinv
    wp_apply (h_selectPassword st pw hpw) as %pwsl %e ⟨%pwb, #Hpwsl, %Hsel⟩
    · isplitr
      · ipureintro; exact Hst
      iexact Hbc
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
      rcases pwSureP_ok Hsp with Hnb | Hsok
      · simp_all
      · cases Hsel.2 Hsok
    | nil =>
      (try wp_auto)
      ihave %Hpk := authOwnF_last_permKeysOk M hs $$ Hown
      have Hstep := (Hok st0 Hl0)
      wp_apply +noauto wp_string_to_bytes as %nsl ⟨Hnsl, -⟩
      ipersist Hnsl
      wp_take_receipt as Hrc
      let urN : UserRec := ⟨name, pwb, [], false, ou, Ho'nn.2⟩
      ihave Hnu : ownUser «$r0_ptr» urN $$ [«$r0»]
      · iunfold ownUser
        iexists _, _, _, _, _, _
        iframe «$r0»
        isplitr
        · iexact Hnsl
        isplitr
        · iexact Hpwsl
        isplitr
        · iapply ownSlice_nil
        · iexact Hopts'
      wp_bind (App (Val #(methods ti.ty go!"UnsafePutUser" ti.v)) (Val #«$r0_ptr»))
      iapply HPutU $$ %st0 %Post %«$r0_ptr» %urN %AuthSess.init [$HL $Hrc $Hsw $Hnu]
      · ipureintro; exact ⟨by decide, List.Pairwise.nil, (List.length_pos_iff.2 hname), Hlen, by simp [urN]⟩
      inext
      iintro ⟨HL, Hsw, -⟩
      (try wp_auto)
      subst Hbnob
      have hstep : userAddF name false st0 = .next (bump (putUserRec st0 urN)) := by
        rw [show putUserRec st0 urN = addUser st0 name false from rfl]; simp [userAddF, hname, Hnone]
      obtain ⟨Hrevfit, Hfit, -⟩ := Hstep
      have Hfit' := (Hfit _ _ rfl hstep).1
      ihave #Hcn := capNextM_step M hs (userAddF name false) st0 (bump (putUserRec st0 urN)) Hl0
        (by rw [hstep]; try simp_all) $$ Hcap
      wp_apply (h_commitRevision st R M P f T Wb ti Lk Sw (putUserRec st0 urN) Post hs st0)
        $$ [$Hinv $HLk $HL $Hown $Hcn] as ⟨%rev, %Hrev, HL, Hown⟩
      · ipureintro
        refine ⟨Hl0, rfl, Hrevfit, fun h1 h2 => permKeysOk_putUserRec _ _ (Hpk st0 Hl0 h1 h2), ?_⟩
        intro hM; subst hM; exact Hl0
      have Hl1 := histLast_after M hs (putUserRec st0 urN) rev (fun h => by subst h; exact Hl0) Hrev
      imod (authSnapF_of_last M _ _ Hl1) $$ Hown with ⟨Hown, #Hsnap⟩
      wp_bind (App (Val (st @!! go.GoType.PointerType authStore.ty @!! go!"refreshRangePermCache"))
        (Val #(GoInterface.ok ti)))
      icases (authOwnF_split _ _).1 $$ Hown with ⟨Hown, HshR⟩
      iapply (h_refresh st R M ti (fun x => Lk x Post) ({ putUserRec st0 urN with revision := rev } : AuthState) (hs ++ [bump (putUserRec st0 urN)]))
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
      icombine Hown HshR as Hown
      ihave Hown := (authOwnF_split _ _).2 $$ Hown
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
      · iexact Hlgnn
      (try wp_auto)
      irename «$r0» => Hresp
      generalize «$r0_ptr» = resp at *
      ihave %Hrespnn := typedPointsto_not_null _ _ _ $$ Hresp
      icases typedPointsto_split _ _ _ $$ Hresp with Hresp
      simp only [TypedPointsto.typedPointstoDef]
      iNamed Hresp
      (try wp_auto)
      wp_apply HUnlock $$ %_ %Post %(hs ++ [bump (putUserRec st0 urN)]) [HL $Hsw $Hown $Hw1 $Hw2]
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
        · ipureintro; exact ⟨fun h => absurd rfl h, fun _ => by assumption⟩
        · iright; iexists _; iexact Header
      iunfold adminOut
      iright
      iexists st0, (.next (bump (putUserRec st0 urN)))
      isplitr
      · ipureintro; exact ⟨Hl0, hstep.symm⟩
      simp only [outRes]
      iframe Hown
  · -- a no-password user: none
    (try wp_auto)
    ihave %Hpk := authOwnF_last_permKeysOk M hs $$ Hown
    have Hstep := (Hok st0 Hl0)
    wp_apply +noauto wp_string_to_bytes as %nsl ⟨Hnsl, -⟩
    ipersist Hnsl
    wp_take_receipt as Hrc
    let urN : UserRec := ⟨name, [], [], true, ou, Ho'nn.2⟩
    ihave Hnu : ownUser «$r0_ptr» urN $$ [«$r0»]
    · iunfold ownUser
      iexists _, _, _, _, _, _
      iframe «$r0»
      isplitr
      · iexact Hnsl
      isplitr
      · iapply ownSlice_nil
      isplitr
      · iapply ownSlice_nil
      · iexact Hopts'
    wp_bind (App (Val #(methods ti.ty go!"UnsafePutUser" ti.v)) (Val #«$r0_ptr»))
    iapply HPutU $$ %st0 %Post %«$r0_ptr» %urN %AuthSess.init [$HL $Hrc $Hsw $Hnu]
    · ipureintro; exact ⟨by decide, List.Pairwise.nil, (List.length_pos_iff.2 hname), Hlen, by simp [urN]⟩
    inext
    iintro ⟨HL, Hsw, -⟩
    (try wp_auto)
    subst Hbnob
    have hstep : userAddF name true st0 = .next (bump (putUserRec st0 urN)) := by
      rw [show putUserRec st0 urN = addUser st0 name true from rfl]; simp [userAddF, hname, Hnone]
    obtain ⟨Hrevfit, Hfit, -⟩ := Hstep
    have Hfit' := (Hfit _ _ rfl hstep).1
    ihave #Hcn := capNextM_step M hs (userAddF name true) st0 (bump (putUserRec st0 urN)) Hl0
      (by rw [hstep]; try simp_all) $$ Hcap
    wp_apply (h_commitRevision st R M P f T Wb ti Lk Sw (putUserRec st0 urN) Post hs st0)
      $$ [$Hinv $HLk $HL $Hown $Hcn] as ⟨%rev, %Hrev, HL, Hown⟩
    · ipureintro
      refine ⟨Hl0, rfl, Hrevfit, fun h1 h2 => permKeysOk_putUserRec _ _ (Hpk st0 Hl0 h1 h2), ?_⟩
      intro hM; subst hM; exact Hl0
    have Hl1 := histLast_after M hs (putUserRec st0 urN) rev (fun h => by subst h; exact Hl0) Hrev
    imod (authSnapF_of_last M _ _ Hl1) $$ Hown with ⟨Hown, #Hsnap⟩
    wp_bind (App (Val (st @!! go.GoType.PointerType authStore.ty @!! go!"refreshRangePermCache"))
      (Val #(GoInterface.ok ti)))
    icases (authOwnF_split _ _).1 $$ Hown with ⟨Hown, HshR⟩
    iapply (h_refresh st R M ti (fun x => Lk x Post) ({ putUserRec st0 urN with revision := rev } : AuthState) (hs ++ [bump (putUserRec st0 urN)]))
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
    icombine Hown HshR as Hown
    ihave Hown := (authOwnF_split _ _).2 $$ Hown
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
    · iexact Hlgnn
    (try wp_auto)
    irename «$r0» => Hresp
    generalize «$r0_ptr» = resp at *
    ihave %Hrespnn := typedPointsto_not_null _ _ _ $$ Hresp
    icases typedPointsto_split _ _ _ $$ Hresp with Hresp
    simp only [TypedPointsto.typedPointstoDef]
    iNamed Hresp
    (try wp_auto)
    wp_apply HUnlock $$ %_ %Post %(hs ++ [bump (putUserRec st0 urN)]) [HL $Hsw $Hown $Hw1 $Hw2]
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
      · ipureintro; exact ⟨fun h => absurd rfl h, fun _ => by assumption⟩
      · iright; iexists _; iexact Header
    iunfold adminOut
    iright
    iexists st0, (.next (bump (putUserRec st0 urN)))
    isplitr
    · ipureintro; exact ⟨Hl0, hstep.symm⟩
    simp only [outRes]
    iframe Hown

end proof

end EtcdGrove
end Perennial
