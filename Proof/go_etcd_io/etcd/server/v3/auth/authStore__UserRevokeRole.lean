/-
Proof of the spec of the same name (the auth plan's S4b, 2026-10-24). Lean-first (no Rocq
counterpart). The loop over the user's roles keeps those other than the revoked one
(`List.filter`), in order, so the roles stay sorted.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.auth.authStore__UserRevokeRole
public import Spec.go_etcd_io.etcd.server.v3.auth.authStore__refreshRangePermCache
public import Spec.go_uber_org.zap.Strings
public import Spec.go_uber_org.zap.Logger__Error
public import Proof.go_etcd_io.etcd.server.v3.auth.AdminLemmas
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

theorem auth.authStore.UserRevokeRole.wp_proof
    (h_commitRevision : auth.authStore.commitRevision.spec (GF := GF) (hG := hG))
    (h_refresh : auth.authStore.refreshRangePermCache.spec (GF := GF) (hG := hG))
    (h_String : zap.String.spec (GF := GF) (hG := hG))
    (h_Strings : zap.Strings.spec (GF := GF) (hG := hG))
    (h_Error : zap.Logger.Error.spec (GF := GF) (hG := hG))
    (h_Info : zap.Logger.Info.spec (GF := GF) (hG := hG)) :
    auth.authStore.UserRevokeRole.spec (GF := GF) (hG := hG) := by
  intro st R M P f T hs Pre Q Post r name role
  wp_start as ⟨#Hinv, #Hr, %Hnamelen, Hown, HWR, Hcs, %Hok⟩
  icases authErrVar_of_init .userNotFound $$ Hpkg with ⟨%eUNF, #HeUNF⟩
  icases authErrVar_of_init .invalidAuthMgmt $$ Hpkg with ⟨%eIAM, #HeIAM⟩
  icases authErrVar_of_init .roleNotGranted $$ Hpkg with ⟨%eRNG, #HeRNG⟩
  simp only [AuthErr.var]
  ihave #Hinv' := Hinv
  iunfold authInv at Hinv'
  icases Hinv' with ⟨%Hst, -, ⟨%lg, #Hlg, %Hlgnn⟩, -, -, -, -⟩
  iunfold userRevokeRoleReqIs at Hr
  icases Hr with ⟨%Hrnn, #HN, #HR⟩
  iunfold authWR at HWR
  icases HWR with ⟨⟨%be, Hbe, #Hbeok⟩, HT, Hen⟩
  iunfold enabledHalf at Hen
  icases Hen with ⟨%en, Hen, #Hev⟩
  ihave #Hbeok' := Hbeok
  iunfold authWBackendOk at Hbeok'
  icases Hbeok' with ⟨%bi, %Hbi, #HBatch, #HFC⟩
  subst Hbi
  wp_apply wp_with_defer as %defer defer
  (try wp_auto)
  wp_join (Q := fun v => iprop(⌜v = #(decide (en = true ∧ name = go!"root" ∧ role = go!"root"))⌝ ∗
      auth.aF go!"enabled" st ↦{DFrac.own (1 : Qp).half} en ∗ r_ptr ↦ r ∗ as_ptr ↦ st))
    at (if: _ then _ else #false) with [Hen r «as»] as ⟨%Hv, Hen, r, «as»⟩
  · cases en
    · (try wp_auto)
      iframe
      ipureintro; simp
    · (try wp_auto)
      (try wp_if_destruct)
      all_goals (try wp_auto)
      all_goals (iframe; ipureintro; simp_all)
  subst Hv
  wp_if_destruct
  · -- `root`'s root role with auth enabled: refused
    obtain ⟨Hen1, Hroot, Hrole⟩ := Hif
    subst Hen1
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
    wp_apply h_Error
    · ipureintro; exact Hlgnn
    (try wp_auto)
    iapply HΦ
    isplitl [Hcs]
    · iapply csContract_noWrite $$ Hcs
    isplitl [Hbe HT Hen]
    · iunfold authWR; iframe HT; isplitl [Hbe]
      · iexists (GoInterface.ok bi); iframe Hbe Hbeok
      · iunfold enabledHalf; iexists true; iframe Hen Hev
    isplitr
    · iunfold respOk; isplitr
      · ipureintro; intro _; rfl
      · ileft; ipureintro; rfl
    iexists true
    iframe Hev
    iunfold adminOut
    iright
    ihave %Hl := authOwn_exists_last M hs $$ Hown
    obtain ⟨st0, Hl⟩ := Hl
    iexists st0, (.err .invalidAuthMgmt)
    isplitr
    · ipureintro
      refine ⟨Hl, ?_⟩
      simp [stepOf, userRevokeRoleF, rootRole, Hroot, Hrole]
    simp only [outRes]
    iframe Hown
    simp only [authErrOf, AuthErr.var]; iexists eIAM; iframe HeIAM; ipureintro; rfl
  have hnr : ¬ (en = true ∧ name = rootRole ∧ role = rootRole) := Hif
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
    isplitl [HPost]
    · ileft; iexact HPost
    isplitl [Hbe HT Hen]
    · iunfold authWR; iframe HT; isplitl [Hbe]
      · iexists (GoInterface.ok bi); iframe Hbe Hbeok
      · iunfold enabledHalf; iexists en; iframe Hen Hev
    isplitr
    · iunfold respOk; isplitr
      · ipureintro; intro _; rfl
      · ileft; ipureintro; rfl
    iexists en
    iframe Hev
    iunfold adminOut
    iright
    iexists st0, (.err .userNotFound)
    isplitr
    · ipureintro
      refine ⟨Hl0, ?_⟩
      simp [stepOf, userRevokeRoleF, hnr, Hnone]
    simp only [outRes, authErrOf, AuthErr.var]
    iframe Hown
    iexists eUNF; iframe HeUNF; ipureintro; rfl
  ihave Hu' := auth.userOut_some_named _ st0 name Hif $$ Hu
  icases Hu' with ⟨%roles, %ur, %Hur, Hu⟩
  obtain ⟨Hlook, Hurn, Hurr, Hsorted⟩ := Hur
  iunfold ownUser at Hu
  icases Hu with ⟨%ums, %unm, %upw, %url, %uo, %uuf, %usc, Hup, #Hunm, #Hupw, #Hurl, #Huo⟩
  icases typedPointsto_split _ _ _ $$ Hup with Hup
  simp only [TypedPointsto.typedPointstoDef]
  iNamed Hup
  (try wp_auto)
  obtain ⟨uu, huu⟩ : ∃ uu, uu = «$r0_ptr» := ⟨_, rfl⟩
  subst huu
  irename «$r0» => Huu
  irename «as» => Has
  irename : (iprop("_" ∷ True) : IProp GF) => Hjunk
  iclear Hjunk
  ihave %Hrl := ownSlice_len _ _ _ $$ Hurl
  -- the roles loop: the updated user's roles are those seen so far but `role`
  let urec : GoSlice → authpb.User := fun sl =>
    { state' := zeroValDef, Name' := unm, Password' := upw, Roles' := sl, Options' := uo,
      unknownFields' := slice.nil, sizeCache' := 0 }
  ihave IH : iprop(∃ (n : w64) (rv : GoString) (sl : GoSlice),
      "i" ∷ i_ptr ↦ n ∗
      "role" ∷ role_ptr ↦ rv ∗
      "Huu" ∷ uu ↦ urec sl ∗
      "Hsl" ∷ sl ↦* ((ur.roles.take (sint.nat n)).filter (fun r => decide (r ≠ role))) ∗
      "Hslc" ∷ ownSliceCap GoString sl (DFrac.own 1) ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.nat n ≤ ur.roles.length⌝)
    $$ [i role Huu]
  · iexists W64 0, _, slice.nil
    iframe
    isplitl []
    · rw [show List.take (sint.nat (W64 0)) ur.roles = [] from rfl, List.filter_nil]
      iapply ownSlice_nil
    isplitl []
    · iapply ownSliceCap_nil
    ipureintro; word
  wp_for IH
  wp_if_destruct
  · -- another role
    have hlt : sint.Z n < sint.Z url.len := by
      first | exact Hif | exact of_decide_eq_true (go.intoVal_inj Hif)
    have hn : sint.nat n < ur.roles.length := by rw [Hrl.1]; word
    obtain ⟨x, hx⟩ : ∃ x, ur.roles[sint.nat n]? = some x := ⟨_, List.getElem?_eq_getElem hn⟩
    have Hbnd : 0 ≤ sint.Z n ∧ sint.Z n < sint.Z url.len := ⟨Hn.1, hlt⟩
    (try wp_auto)
    simp only [Hbnd, _root_.and_self, ↓reduceIte]
    wp_apply wp_load_slice_index url (sint.Z n) ur.roles .discard x Hn.1 $$ [$Hurl] as -
    · iframe; ipureintro; exact hx
    (try wp_auto)
    have hsucc : sint.nat (n + W64 1) = sint.nat n + 1 := by word
    wp_if_destruct
    · -- the revoked role: skipped
      (try wp_auto)
      wp_for_post
      iframe
      iexists n + W64 1, x, sl
      iframe
      isplitl [Hsl]
      · have hx' : ¬ (x ≠ role) := by first | exact fun h => h Hif | (intro h; exact h (by simpa using Hif)) | simpa using Hif
        rw [hsucc, auth.filter_take_succ _ _ _ _ hx, if_neg hx', List.append_nil]; iexact Hsl
      ipureintro; constructor <;> word
    · -- kept
      (try wp_auto)
      wp_apply wp_slice_literal (V := GoString) [x]
      isplitr
      · ipureintro; rfl
      iintro %xs ⟨Hxs, -⟩
      (try wp_auto)
      wp_apply wp_slice_append sl _ _ [x] (DFrac.own 1) $$ [$Hsl $Hslc $Hxs] as %sl' ⟨Hsl, Hslc, -⟩
      (try wp_auto)
      wp_for_post
      iframe
      iexists n + W64 1, x, sl'
      iframe
      isplitl [Hsl]
      · rw [hsucc, auth.filter_take_succ _ _ _ _ hx, if_pos (show x ≠ role from Hif)]
        iExactEq Hsl
        all_goals simp
      ipureintro; constructor <;> word
  -- the loop is over: every role seen
  have hall : sint.nat n = ur.roles.length := by
    have : ¬ sint.Z n < sint.Z url.len := by
      first | exact Hif | exact fun h => Hif (by simpa using h)
    rw [Hrl.1]; word
  rw [hall, List.take_length] at *
  obtain ⟨roles', hroles'⟩ : ∃ l, l = ur.roles.filter (fun r => decide (r ≠ role)) := ⟨_, rfl⟩
  ihave Hsl : sl ↦* roles' $$ [Hsl]
  · rw [hroles']; iexact Hsl
  ihave %Hsll := ownSlice_len _ _ _ $$ Hsl
  (try wp_auto)
  have hlen_iff := auth.filter_ne_length_eq_iff ur.roles role
  rw [← hroles'] at hlen_iff
  wp_if_destruct
  · -- nothing revoked: `ErrRoleNotGranted`
    have hnot : role ∉ ur.roles := by
      apply hlen_iff.mp
      have h1 := Hsll.1; have h2 := Hrl.1
      first | (rw [h1, h2]; word) | (revert Hif; word) | omega
    wp_apply HUnlock $$ %st0 %Post %hs [$HL $Hown] as ⟨HPost, HT, Hown⟩
    · ipureintro; exact Hl0
    (try wp_auto)
    iapply HΦ
    isplitl [HPost]
    · ileft; iexact HPost
    isplitl [Hbe HT Hen]
    · iunfold authWR; iframe HT; isplitl [Hbe]
      · iexists (GoInterface.ok bi); iframe Hbe Hbeok
      · iunfold enabledHalf; iexists en; iframe Hen Hev
    isplitr
    · iunfold respOk; isplitr
      · ipureintro; intro _; rfl
      · ileft; ipureintro; rfl
    iexists en
    iframe Hev
    iunfold adminOut
    iright
    iexists st0, (.err .roleNotGranted)
    isplitr
    · ipureintro
      refine ⟨Hl0, ?_⟩
      have : role ∉ roles := Hurr ▸ hnot
      simp [stepOf, userRevokeRoleF, hnr, Hlook, this]
    simp only [outRes, authErrOf, AuthErr.var]
    iframe Hown
    iexists eRNG; iframe HeRNG; ipureintro; rfl
  have hin : role ∈ ur.roles := by
    refine Classical.byContradiction fun hnot => ?_
    apply Hif
    have h1 := (hlen_iff.mpr hnot)
    have h2 := Hsll.1; have h3 := Hrl.1
    first | (congr 1; word) | word | (rw [h2, h3]; congr 1; word)
  -- the updated user put
  imod (ownSlice_persist _ _ _) $$ Hsl with #Hsl'
  have hsorted' : roles'.Pairwise go.GoStringLt := by rw [hroles']; exact (Hurr ▸ Hsorted).filter _
  wp_bind (App (Val #(methods ti.ty go!"UnsafePutUser" ti.v)) (Val #uu))
  iapply HPutU $$ %st0 %Post %uu
    %({ name := ur.name, password := ur.password, roles := roles', noPassword := ur.noPassword } : UserRec)
    [HL Huu]
  · iframe HL
    isplitl [Huu]
    · iunfold ownUser
      iexists zeroValDef, unm, upw, sl, uo, slice.nil, (0 : w32)
      iframe Huu Hunm Hupw Hsl' Huo
    ipureintro; exact ⟨hsorted', by rw [Hurn]; exact Hnamelen⟩
  inext
  iintro ⟨HL, Huu⟩
  (try wp_auto)
  ihave %Hpk := authOwnF_last_permKeysOk M hs $$ Hown
  have Hstep := Hok en st0 Hl0
  have hstep : userRevokeRoleF en name role st0 = .next (bump (putUser st0 name roles')) := by
    have : role ∈ roles := Hurr ▸ hin
    simp only [userRevokeRoleF, hnr, Hlook, this, if_false, if_true, hroles', Hurr]
  ihave HL : Lk (putUser st0 name roles') Post $$ [HL]
  · iExactEq HL; rw [Hurn]
  obtain ⟨Hrevfit, Hfit⟩ := Hstep
  have Hfit' := Hfit _ _ rfl hstep
  wp_apply (h_commitRevision st R M P f T ti Lk (putUser st0 name roles') Post hs st0)
    $$ [$Hinv $HLk $HL $Hown] as ⟨%rev, %Hrev, HL, Hown⟩
  · ipureintro
    refine ⟨Hl0, rfl, Hrevfit, fun h1 h2 => permKeysOk_putUser _ _ _ (Hpk st0 Hl0 h1 h2), ?_⟩
    intro hM; subst hM; exact Hl0
  have Hl1 := histLast_after M hs (putUser st0 name roles') rev (fun h => by subst h; exact Hl0) Hrev
  imod (authSnapF_of_last M _ _ Hl1) $$ Hown with ⟨Hown, #Hsnap⟩
  (try wp_auto)
  wp_bind (App (Val (st @!! go.GoType.PointerType authStore.ty @!! go!"refreshRangePermCache"))
    (Val #(GoInterface.ok ti)))
  iapply (h_refresh st R M ti (fun x => Lk x Post)
      ({ putUser st0 name roles' with revision := rev } : AuthState))
    $$ [HL]
  · iframe Hpkg Hinv
    isplitr
    · iapply HRd
    isplitl [HL]
    · iExactEq HL
      all_goals rfl
    iframe Hsnap
    ipureintro; exact permsFit_rev _ rev Hfit'
  inext
  iintro HL
  (try wp_auto)
  wp_apply h_String _ _ as %f1 -
  (try wp_auto)
  wp_apply h_Strings _ _ as %f2 -
  (try wp_auto)
  iunfold ownUser at Huu
  icases Huu with ⟨%ums', %unm', %upw', %url', %uo', %uuf', %usc', Huu, -, -, -, -⟩
  icases typedPointsto_split _ _ _ $$ Huu with Huu
  simp only [TypedPointsto.typedPointstoDef]
  iNamed Huu
  (try wp_auto)
  wp_apply h_Strings _ _ as %f3 -
  (try wp_auto)
  wp_apply h_String _ _ as %f4 -
  (try wp_auto)
  wp_apply wp_slice_literal (V := go_uber_org.zap.zapcore.Field) [f1, f2, f3, f4]
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
  wp_apply HUnlock $$ %_ %Post %(hs ++ [bump (putUser st0 name roles')]) [HL $Hown]
    as ⟨HPost, HT, Hown⟩
  · isplitl [HL]
    · iExactEq HL
      all_goals rfl
    ipureintro; exact Hl1
  (try wp_auto)
  iapply HΦ
  isplitl [HPost]
  · ileft; iexact HPost
  isplitl [Hbe HT Hen]
  · iunfold authWR; iframe HT; isplitl [Hbe]
    · iexists (GoInterface.ok bi); iframe Hbe Hbeok
    · iunfold enabledHalf; iexists en; iframe Hen Hev
  isplitl [Header]
  · iunfold respOk; isplitr
    · ipureintro; intro h; exact absurd rfl h
    · iright; iexists _; iexact Header
  iexists en
  iframe Hev
  iunfold adminOut
  iright
  iexists st0, (.next (bump (putUser st0 name roles')))
  isplitr
  · ipureintro; exact ⟨Hl0, hstep.symm⟩
  simp only [outRes]
  isplitl [Hown]
  · iExactEq Hown
    all_goals rfl
  · ipureintro; trivial

end proof

end EtcdGrove
end Perennial
