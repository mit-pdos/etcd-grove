/-
`UserAdd.specTSure` (the auth plan's E2y, 2026-10-26): E2s's `UserAdd.specT` (the admin side's
halves of the flag and the cache kept tied to the latest state) and E2u's `UserAdd.specSure` (a
request whose password choice cannot fail, `userAddSure`, never gets `ErrNoPasswordUser`) in one
triple: `specT`'s with `userAddSure` in the precondition and the step's outcome alone (`noExtra`)
in the post. The proof is `UserAdd.wp_tie`'s with `wp_sure`'s `selectPassword` case. Lean-first
(no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.auth.authStore__UserAdd
public import Proof.go_etcd_io.etcd.server.v3.auth.authStore__UserAdd_sure

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.auth auth go_etcd_io.etcd.api.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- `UserAdd.specT` of a request whose password choice cannot fail (`userAddSure`): no
`ErrNoPasswordUser` (`noExtra`). -/
abbrev auth.authStore.UserAdd.specTSure : Prop :=
  ∀ (st : Loc) (R : IProp GF) (M : AuthMode) (P : IProp GF) (f : val) (T : IProp GF)
    (hs : List AuthState) (Pre Q Post : IProp GF) (r : Loc) (name : GoString) (b0 : Bool) (sc0 : AuthState),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth ∗ authInv st R M ∗ userAddReqIs r name ∗ userAddSure r ∗ ⌜name.length ≤ backend.maxKeySize⌝ ∗ authOwn M hs ∗ authWRx st M P f T b0 sc0 ∗ mvcc.csContract P f Pre Q Post ∗
      ⌜stepOk M hs (stepOf (userAddF name))⌝ ∗ capNextM M hs (stepOf (userAddF name)) }}
    (App (Val (st @!! go.GoType.PointerType authStore.ty @!! go!"UserAdd")) (Val #r))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); ∃ (b : Bool) (sc : AuthState), (Post ∨ Pre) ∗ authWRx st M P f T b sc ∗
      respOk etcdserverpb.AuthUserAddResponse resp err ∗ adminOutP M hs (stepOf (userAddF name)) noExtra err (tieStep M hs b0 sc0 b sc) }}

/-- `UserAdd.specTSure` keeping the store's backend `be` (`authWRxB`; the auth plan's E3l). -/
abbrev auth.authStore.UserAdd.specTSureB : Prop :=
  ∀ (st : Loc) (R : IProp GF) (M : AuthMode) (P : IProp GF) (f : val) (T : IProp GF)
    (hs : List AuthState) (Pre Q Post : IProp GF) (r : Loc) (name : GoString) (b0 : Bool) (sc0 : AuthState) (be : AuthBackend),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth ∗ authInv st R M ∗ userAddReqIs r name ∗ userAddSure r ∗ ⌜name.length ≤ backend.maxKeySize⌝ ∗ authOwn M hs ∗ authWRxB st M P f T b0 sc0 be ∗ mvcc.csContract P f Pre Q Post ∗
      ⌜stepOk M hs (stepOf (userAddF name))⌝ ∗ capNextM M hs (stepOf (userAddF name)) }}
    (App (Val (st @!! go.GoType.PointerType authStore.ty @!! go!"UserAdd")) (Val #r))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); ∃ (b : Bool) (sc : AuthState), (Post ∨ Pre) ∗ authWRxB st M P f T b sc be ∗
      respOk etcdserverpb.AuthUserAddResponse resp err ∗ adminOutP M hs (stepOf (userAddF name)) noExtra err (tieStep M hs b0 sc0 b sc) }}

theorem auth.authStore.UserAdd.specTSure_of_TB [package_sem : go_etcd_io.etcd.server.v3.auth.Assumptions]
    (h : auth.authStore.UserAdd.specTSureB (GF := GF) (hG := hG)) :
    auth.authStore.UserAdd.specTSure (GF := GF) (hG := hG) := by
  intro st R M P f T hs Pre Q Post r name b0 sc0
  iintro %Φ ⟨#Hpkg, #Hinv, #Hr, #Hsure, %Hlen, Hown, HWR, Hcs, %Hok, #Hcap⟩ HΦ
  ihave ⟨%be, HWR⟩ := authWRx_B st M P f T b0 sc0 $$ HWR
  iapply (h st R M P f T hs Pre Q Post r name b0 sc0 be) $$ [Hown HWR Hcs]
  · iframe; iframe #; ipureintro; exact ⟨Hlen, Hok⟩
  iintro !> %resp %err ⟨%b, %sc, HPP, HWR, Hrest⟩
  iapply HΦ
  iexists b, sc
  iframe HPP Hrest
  iapply authWRx_of_B $$ HWR

end spec

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.auth.Assumptions]

theorem auth.authStore.UserAdd.wp_tieSureB
    (h_commitRevision : auth.authStore.commitRevision.spec (GF := GF) (hG := hG))
    (h_refresh : auth.authStore.refreshRangePermCache.spec (GF := GF) (hG := hG))
    (h_selectPassword : auth.authStore.selectPassword.spec (GF := GF) (hG := hG))
    (h_String : zap.String.spec (GF := GF) (hG := hG))
    (h_Info : zap.Logger.Info.spec (GF := GF) (hG := hG)) :
    auth.authStore.UserAdd.specTSureB (GF := GF) (hG := hG) := by
  intro st R M P f T hs Pre Q Post r name b0 sc0 be
  wp_start as ⟨#Hinv, #Hr, #Hsure, %Hlen, Hown, HWR, Hcs, %Hok, #Hcap⟩
  icases authErrVar_of_init .userEmpty $$ Hpkg with ⟨%eUE, #HeUE⟩
  icases authErrVar_of_init .userAlreadyExist $$ Hpkg with ⟨%eUAE, #HeUAE⟩
  icases authErrVar_of_init .noPasswordUser $$ Hpkg with ⟨%eNPU, #HeNPU⟩
  simp only [AuthErr.var]
  ihave #Hinv' := Hinv
  iunfold authInv at Hinv'
  icases Hinv' with ⟨%Hst, -, ⟨%lg, #Hlg, %Hlgnn⟩, -, -, -, -⟩
  iunfold userAddReqIs at Hr
  icases Hr with ⟨%Hrnn, #HN, ⟨%pw, %hpw, #Hpw, #Hhpw⟩, ⟨%o, %nob, #Ho, #Hopts⟩⟩
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
    iexists st0, (.err .userEmpty)
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
    iexists st0, (.err .userAlreadyExist)
    isplitr
    · ipureintro; exact tieStep_same _ _ _ _
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
      ihave #Hcn := capNextM_step M hs (userAddF name) st0 (bump (putUser st0 urN.name urN.roles)) Hl0
        (by rw [hstep]; try simp_all) $$ Hcap
      wp_apply (h_commitRevision st R M P f T ti Lk (putUser st0 urN.name urN.roles) Post hs st0)
        $$ [$Hinv $HLk $HL $Hown $Hcn] as ⟨%rev, %Hrev, HL, Hown⟩
      · ipureintro
        refine ⟨Hl0, rfl, Hrevfit, fun h1 h2 => permKeysOk_putUser _ _ _ (Hpk st0 Hl0 h1 h2), ?_⟩
        intro hM; subst hM; exact Hl0
      have Hl1 := histLast_after M hs (putUser st0 urN.name urN.roles) rev (fun h => by subst h; exact Hl0) Hrev
      imod (authSnapF_of_last M _ _ Hl1) $$ Hown with ⟨Hown, #Hsnap⟩
      wp_bind (App (Val (st @!! go.GoType.PointerType authStore.ty @!! go!"refreshRangePermCache"))
        (Val #(GoInterface.ok ti)))
      iapply (h_refresh st R M ti (fun x => Lk x Post) ({ putUser st0 urN.name urN.roles with revision := rev } : AuthState) (hs ++ [bump (putUser st0 urN.name urN.roles)]))
        $$ [HL Hca Hown]
      · iframe Hpkg Hinv
        isplitl [Hca]
        · iapply (cacheHalf_of_at _ _ _) $$ Hca Hcsn
        isplitr
        · iapply HRd
        isplitl [HL]
        · iExactEq HL; rfl
        iframe Hsnap
        iframe Hown; ipureintro; exact ⟨permsFit_rev _ rev Hfit', fun _ h => by subst h; exact Hl1⟩
      inext
      iintro ⟨HL, Hca, Hown⟩
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
      iexists b0, ({ putUser st0 urN.name urN.roles with revision := rev } : AuthState)
      isplitl [HPost]
      · ileft; iexact HPost
      isplitl [Hbe HT Hfl Hca]
      · iunfold authWRxB; iframe HT Hfl Hev Hca Hsnap; iframe Hbe Hbeok
      isplitl [Header]
      · iunfold respOk; isplitr
        · ipureintro; intro h; exact absurd rfl h
        · iright; iexists _; iexact Header
      iunfold adminOutP
      iright
      iexists st0, (.next (bump (putUser st0 name [])))
      isplitr
      · ipureintro; exact tieStep_refresh M hs _ b0 sc0 _ st0 Hl0 Hl1 rfl
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
    ihave #Hcn := capNextM_step M hs (userAddF name) st0 (bump (putUser st0 urN.name urN.roles)) Hl0
      (by rw [hstep]; try simp_all) $$ Hcap
    wp_apply (h_commitRevision st R M P f T ti Lk (putUser st0 urN.name urN.roles) Post hs st0)
      $$ [$Hinv $HLk $HL $Hown $Hcn] as ⟨%rev, %Hrev, HL, Hown⟩
    · ipureintro
      refine ⟨Hl0, rfl, Hrevfit, fun h1 h2 => permKeysOk_putUser _ _ _ (Hpk st0 Hl0 h1 h2), ?_⟩
      intro hM; subst hM; exact Hl0
    have Hl1 := histLast_after M hs (putUser st0 urN.name urN.roles) rev (fun h => by subst h; exact Hl0) Hrev
    imod (authSnapF_of_last M _ _ Hl1) $$ Hown with ⟨Hown, #Hsnap⟩
    wp_bind (App (Val (st @!! go.GoType.PointerType authStore.ty @!! go!"refreshRangePermCache"))
      (Val #(GoInterface.ok ti)))
    iapply (h_refresh st R M ti (fun x => Lk x Post) ({ putUser st0 urN.name urN.roles with revision := rev } : AuthState) (hs ++ [bump (putUser st0 urN.name urN.roles)]))
      $$ [HL Hca Hown]
    · iframe Hpkg Hinv
      isplitl [Hca]
      · iapply (cacheHalf_of_at _ _ _) $$ Hca Hcsn
      isplitr
      · iapply HRd
      isplitl [HL]
      · iExactEq HL; rfl
      iframe Hsnap
      iframe Hown; ipureintro; exact ⟨permsFit_rev _ rev Hfit', fun _ h => by subst h; exact Hl1⟩
    inext
    iintro ⟨HL, Hca, Hown⟩
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
    iexists b0, ({ putUser st0 urN.name urN.roles with revision := rev } : AuthState)
    isplitl [HPost]
    · ileft; iexact HPost
    isplitl [Hbe HT Hfl Hca]
    · iunfold authWRxB; iframe HT Hfl Hev Hca Hsnap; iframe Hbe Hbeok
    isplitl [Header]
    · iunfold respOk; isplitr
      · ipureintro; intro h; exact absurd rfl h
      · iright; iexists _; iexact Header
    iunfold adminOutP
    iright
    iexists st0, (.next (bump (putUser st0 name [])))
    isplitr
    · ipureintro; exact tieStep_refresh M hs _ b0 sc0 _ st0 Hl0 Hl1 rfl
    isplitr
    · ipureintro; exact ⟨Hl0, hstep.symm⟩
    simp only [outRes]
    iframe Hown

theorem auth.authStore.UserAdd.wp_tieSure
    (h_commitRevision : auth.authStore.commitRevision.spec (GF := GF) (hG := hG))
    (h_refresh : auth.authStore.refreshRangePermCache.spec (GF := GF) (hG := hG))
    (h_selectPassword : auth.authStore.selectPassword.spec (GF := GF) (hG := hG))
    (h_String : zap.String.spec (GF := GF) (hG := hG))
    (h_Info : zap.Logger.Info.spec (GF := GF) (hG := hG)) :
    auth.authStore.UserAdd.specTSure (GF := GF) (hG := hG) :=
  auth.authStore.UserAdd.specTSure_of_TB (auth.authStore.UserAdd.wp_tieSureB h_commitRevision h_refresh h_selectPassword h_String h_Info)

end proof

end EtcdGrove
end Perennial
