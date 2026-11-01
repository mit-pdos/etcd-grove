/-
Proof of the spec of the same name (the auth plan's S4c, 2026-10-24). Lean-first (no Rocq
counterpart). The user's message is the caller's (`userOutX`, the write side's read): its roles
get the new one appended and are sorted in place (`sort.Strings`), a permutation sorted strictly
since the role was not there (`pairwise_lt_of_sorted_perm`).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.auth.authStore__UserGrantRole
public import Proof.go_etcd_io.etcd.server.v3.auth.LatestTie
public import Spec.go_etcd_io.etcd.server.v3.auth.authStore__refreshRangePermCache
public import Spec.go_uber_org.zap.Strings
public import Spec.go_uber_org.zap.Logger__Warn
public import Proof.go_etcd_io.etcd.server.v3.auth.AdminLemmas
public import Proof.go_etcd_io.etcd.server.v3.auth.GrantLemmas
public import Proof.go_etcd_io.etcd.server.v3.auth.hasRootRole
public import Spec.go_etcd_io.etcd.server.v3.auth.authStore__commitRevision
public import Spec.go_uber_org.zap.String
public import Spec.go_uber_org.zap.Logger__Info
public import Perennial.Proof.sort.Link
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

theorem auth.authStore.UserGrantRole.wp_tieB
    (h_commitRevision : auth.authStore.commitRevision.spec (GF := GF) (hG := hG))
    (h_refresh : auth.authStore.refreshRangePermCache.spec (GF := GF) (hG := hG))
    (h_String : zap.String.spec (GF := GF) (hG := hG))
    (h_Strings : zap.Strings.spec (GF := GF) (hG := hG))
    (h_Warn : zap.Logger.Warn.spec (GF := GF) (hG := hG))
    (h_Info : zap.Logger.Info.spec (GF := GF) (hG := hG)) :
    auth.authStore.UserGrantRole.specTB (GF := GF) (hG := hG) := by
  intro st R M P f T hs Pre Q Post r user rn b0 sc0 be
  wp_start as ⟨#Hinv, #Hr, %Hnamelen, Hown, HWR, Hcs, %Hbound, %Hok, #Hcap⟩
  icases authErrVar_of_init .userNotFound $$ Hpkg with ⟨%eUNF, #HeUNF⟩
  icases authErrVar_of_init .roleNotFound $$ Hpkg with ⟨%eRNF, #HeRNF⟩
  simp only [AuthErr.var]
  ihave #Hsortpkg : isPkgInit (PROP := IProp GF) pkg_id.sort $$ []
  · iPkgInit
  ihave #Hinv' := Hinv
  iunfold authInv at Hinv'
  icases Hinv' with ⟨%Hst, -, ⟨%lg, #Hlg, %Hlgnn⟩, -, -, -, -⟩
  iunfold userGrantRoleReqIs at Hr
  icases Hr with ⟨%Hrnn, #HU, #HR⟩
  iunfold authWRxB at HWR
  icases HWR with ⟨⟨Hbe, #Hbeok⟩, HT, Hfl, #Hev, Hca, #Hcsn⟩
  ihave #Hbeok' := Hbeok
  iunfold authWBackendOk at Hbeok'
  icases Hbeok' with ⟨%bi, %Hbi, #HBatch, #HFC⟩
  subst Hbi
  wp_auto
  wp_apply wp_with_defer as %defer defer
  (try wp_auto)
  wp_apply HBatch as %tx Htx
  iunfold authBatchTxOk at Htx
  icases Htx with ⟨%ti, %Hti, %Lk, #HLk⟩
  subst Hti
  ihave #HLk' := HLk
  iunfold authBatchTxLk at HLk'
  icases HLk' with ⟨#HLock, #HRd, #HPutU, -, -, -, -, -, #HUnlock, #HUGX, -⟩
  (try wp_auto)
  wp_bind (App (Val #(methods ti.ty go!"Lock" ti.v)) (Val #()))
  iapply HLock $$ %hs %Pre %Q %Post [$Hcs $HT $Hown]
  inext
  iintro ⟨%st0, HL, Hown, %Hl0⟩
  ihave #HRd' := HRd $$ %Post
  iunfold authReaderOk at HRd'
  icases HRd' with ⟨-, #HRG, -, -, -⟩
  (try wp_auto)
  wp_bind (App (Val #(methods ti.ty go!"UnsafeGetUser" ti.v)) (Val #user))
  iapply HUGX $$ %st0 %Post %user HL
  inext
  iintro %u ⟨HL, Hu⟩
  (try wp_auto)
  wp_if_destruct
  · -- no such user
    ihave %Hnone := userOutX_null st0 user $$ Hu
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
    iexists st0, (.err .userNotFound)
    isplitr
    · ipureintro; exact tieStep_same _ _ _ _
    isplitr
    · ipureintro
      refine ⟨Hl0, ?_⟩
      simp [userGrantRoleR, Hnone]
    simp only [outRes, authErrOf, AuthErr.var]
    iframe Hown
    iexists eUNF; iframe HeUNF; ipureintro; rfl
  have hunn : u ≠ null := Hif
  ihave Hu' := auth.userOutX_some_named _ st0 user Hif $$ Hu
  icases Hu' with ⟨%roles, %ur, %Hur, Hu⟩
  obtain ⟨Hlook, Hurn, Hurr, Hsorted⟩ := Hur
  (try wp_auto)
  obtain ⟨rn0, hrn0⟩ : ∃ x, x = rn := ⟨_, rfl⟩
  obtain ⟨rt, hrt⟩ : ∃ x : GoString, x = go!"root" := ⟨_, rfl⟩
  rw [← hrt]
  subst hrn0
  wp_if_destruct
  rotate_left
  -- a role other than `root`: it must exist
  (try wp_auto)
  wp_bind (App (Val #(methods ti.ty go!"UnsafeGetRole" ti.v)) (Val #rn0))
  iapply HRG $$ %st0 %rn0 HL
  inext
  iintro %rl ⟨HL, Hrl⟩
  (try wp_auto)
  wp_if_destruct
  · ihave %Hrnone := roleOut_null st0 rn0 $$ Hrl
    (try wp_auto)
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
    iexists st0, (.err .roleNotFound)
    isplitr
    · ipureintro; exact tieStep_same _ _ _ _
    isplitr
    · ipureintro
      refine ⟨Hl0, ?_⟩
      have hnr : rn0 ≠ rootRole := fun h => Hif (h.trans hrt.symm)
      simp [userGrantRoleR, Hlook, Hrnone, hnr]
    simp only [outRes, authErrOf, AuthErr.var]
    iframe Hown
    iexists eRNF; iframe HeRNF; ipureintro; rfl
  ihave Hrl' := roleOut_some rl st0 rn0 Hif $$ Hrl
  icases Hrl' with ⟨%ps, %rr, %Hrr, -⟩
  have hrole : rn0 = rootRole ∨ (st0.roles !! rn0).isSome := by
    right; rw [Hrr.1]; rfl
  (try wp_auto)
  rotate_left
  have hrole : rn0 = rootRole ∨ (st0.roles !! rn0).isSome := by
    have h : rn0 = rt := by simpa using Hif
    exact Or.inl (h.trans hrt)
  all_goals (
      -- the common tail
      iunfold ownUserX at Hu
      icases Hu with ⟨%ums, %unm, %upw, %url, %uo, %uuf, %usc, Hup, #Hunm, #Hupw, Hurl, Hurlc, #Huo⟩
      icases typedPointsto_split _ _ _ $$ Hup with Hup
      simp only [TypedPointsto.typedPointstoDef]
      iNamed Hup
      (try wp_auto)
      wp_apply (_root_.Perennial.sort.wp_SearchStrings url _ (DFrac.own 1) ur.roles)
        $$ [$Hurl] as %i ⟨Hurl, %Hbnd, %Hlo, %Hhi⟩
      · ipureintro; exact auth.listSorted_of_pairwise_lt _ (Hurr ▸ Hsorted)
      ihave %Hl := ownSlice_len _ _ _ $$ Hurl
      have hmem := auth.mem_iff_search ur.roles _ (sint.Z i).toNat (Hurr ▸ Hsorted)
        (fun j x0 hj hx => Hlo j x0 (by omega) hx) (fun j x0 hj hx => Hhi j x0 (by omega) hx)
      (try wp_auto)
      wp_join (Q := fun v => iprop(⌜v = #(decide (rn0 ∈ ur.roles))⌝ ∗ user_ptr ↦ u ∗
          structFieldRef authpb.User go!"Roles" u ↦ url ∗ url ↦* ur.roles ∗ idx_ptr ↦ i ∗ r_ptr ↦ r))
        at (if: _ then _ else #false) with [user Roles Hurl idx r] as ⟨%Hv, user, Roles, Hurl, idx, r⟩
      · wp_if_destruct
        · have hlt : (sint.Z i).toNat < ur.roles.length := by have := Hl.1; word
          obtain ⟨x, hx⟩ : ∃ x, ur.roles[(sint.Z i).toNat]? = some x :=
            ⟨_, List.getElem?_eq_getElem hlt⟩
          have Hb : 0 ≤ sint.Z i ∧ sint.Z i < sint.Z url.len := ⟨Hbnd.1, Hif⟩
          simp only [Hb, _root_.and_self, ↓reduceIte]
          wp_apply wp_load_slice_index url (sint.Z i) ur.roles (DFrac.own 1) x Hbnd.1 $$ [$Hurl] as Hurl
          · ipureintro; exact hx
          (try wp_auto)
          iframe
          ipureintro
          congr 1
          rw [List.getElem?_eq_getElem hlt, Option.some.injEq] at hx
          by_cases hxr : x = rn0
          · have : rn0 ∈ ur.roles := hmem.mpr ⟨hlt, by rw [hx, hxr]⟩
            simp [hxr, this]
          · have : rn0 ∉ ur.roles := fun hm => hxr (by
              obtain ⟨_, h⟩ := hmem.mp hm; rw [← hx]; exact h)
            simp [hxr, this]
        · (try wp_auto)
          iframe
          ipureintro
          have : rn0 ∉ ur.roles := fun hm => by
            obtain ⟨h, _⟩ := hmem.mp hm
            have := Hl.1; apply Hif; word
          simp [this]
      subst Hv
      wp_if_destruct
      · -- the user has the role: ignored
        (try wp_auto)
        wp_apply h_String _ _ as %f1 -
        (try wp_auto)
        wp_apply h_Strings _ _ as %f2 -
        (try wp_auto)
        wp_apply h_String _ _ as %f3 -
        (try wp_auto)
        wp_apply wp_slice_literal (V := go_uber_org.zap.zapcore.Field) [f1, f2, f3]
        isplitr
        · ipureintro; rfl
        iintro %fsl ⟨-, -⟩
        (try wp_auto)
        wp_apply h_Warn
        · ipureintro; exact Hlgnn
        (try wp_auto)
        irename «$r0» => Hresp
        generalize «$r0_ptr» = resp at *
        icases typedPointsto_split _ _ _ $$ Hresp with Hresp
        simp only [TypedPointsto.typedPointstoDef]
        iNamed Hresp
        (try wp_auto)
        wp_apply HUnlock $$ %st0 %Post %hs [$HL $Hown] as ⟨HPost, HT, Hown⟩
        · ipureintro; exact Hl0
        (try wp_auto)
        iapply HΦ
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
        iexists st0, .same
        isplitr
        · ipureintro; exact tieStep_same _ _ _ _
        isplitr
        · ipureintro
          refine ⟨Hl0, ?_⟩
          have hin : rn0 ∈ roles := Hurr ▸ Hif
          simp only [userGrantRoleR, Hlook]
          rcases hrole with h | h
          · subst h; simp [hin]
          · cases hh : st0.roles !! rn0 with
            | none => rw [hh] at h; exact absurd h (by decide)
            | some _ => simp [hh, hin]
        simp only [outRes]
        iframe Hown
      -- granted: the role appended, the roles sorted
      have hnin : rn0 ∉ ur.roles := Hif
      (try wp_auto)
      wp_apply wp_slice_literal (V := GoString) [rn0]
      isplitr
      · ipureintro; rfl
      iintro %sl1 ⟨Hsl1, -⟩
      (try wp_auto)
      wp_apply (wp_slice_append url ur.roles _ [rn0] (DFrac.own 1)) $$ [$Hurl $Hurlc $Hsl1]
        as %s2 ⟨Hs2, Hs2c, -⟩
      (try wp_auto)
      have hlen : (ur.roles ++ [rn0]).length ≤ 2 ^ 62 := by
        have := Hbound st0 roles Hl0 Hlook
        rw [List.length_append, Hurr]; simp only [List.length_singleton]; omega
      wp_apply (_root_.Perennial.sort.wp_Strings s2 (ur.roles ++ [rn0])) $$ [$Hs2]
        as %xs' ⟨Hs2, %Hperm, %Hsrt⟩
      · ipureintro; exact hlen
      have hxs : xs'.Pairwise go.GoStringLt :=
        auth.pairwise_lt_of_sorted_perm (ur.roles ++ [rn0]) xs'
          (List.nodup_append.mpr ⟨auth.nodup_of_pairwise_lt _ (Hurr ▸ Hsorted), (by simp),
            fun a ha b hb => by simp at hb; subst hb; exact fun he => hnin (he ▸ ha)⟩)
          Hperm.symm Hsrt
      imod (ownSlice_persist _ _ _) $$ Hs2 with #Hs2
      (try wp_auto)
      let msgN : authpb.User := authpb.User.mk ums unm upw s2 uo uuf usc
      ihave Hup : u ↦ msgN $$ [state Name Password Roles Options unknownFields sizeCache]
      · iapply typedPointsto_combine u _ _ hunn
        simp only [TypedPointsto.typedPointstoDef]
        iframe
      let urN : UserRec := UserRec.mk ur.name ur.password xs' ur.noPassword
      have hstepR : userGrantRoleR user rn0 st0 (.next (bump (putUser st0 user xs'))) := by
        simp only [userGrantRoleR, Hlook]
        have hnin' : rn0 ∉ roles := Hurr ▸ hnin
        have hc : ¬ (rn0 ≠ rootRole ∧ (st0.roles !! rn0).isNone = true) := by
          rintro ⟨h1, h2⟩
          rcases hrole with h | h
          · exact h1 h
          · cases hh : st0.roles !! rn0 <;> simp_all
        rw [if_neg hc, if_neg hnin']
        exact ⟨xs', by rw [← Hurr]; exact Hperm.symm, hxs, rfl⟩
      wp_bind (App (Val #(methods ti.ty go!"UnsafePutUser" ti.v)) (Val #u))
      iapply HPutU $$ %st0 %Post %u %urN [HL Hup]
      · iframe HL
        isplitl [Hup]
        · iunfold ownUser
          iexists ums, unm, upw, s2, uo, uuf, usc
          iframe Hup Hunm Hupw Hs2 Huo
        ipureintro; exact ⟨hxs, by show ur.name.length ≤ _; rw [Hurn]; exact Hnamelen⟩
      inext
      iintro ⟨HL, Huu⟩
      (try wp_auto)
      ihave %Hpk := authOwnF_last_permKeysOk M hs $$ Hown
      have Hstep := Hok st0 Hl0
      ihave HL : Lk (putUser st0 user xs') Post $$ [HL]
      · iExactEq HL; rw [Hurn]
      obtain ⟨Hrevfit, Hfit⟩ := Hstep
      have Hfit' := Hfit _ _ hstepR rfl
      ihave #Hcn := capNextM_use M hs _ st0 _ Hl0 hstepR $$ Hcap
      wp_apply (h_commitRevision st R M P f T ti Lk (putUser st0 user xs') Post hs st0)
        $$ [$Hinv $HLk $HL $Hown $Hcn] as ⟨%rev, %Hrev, HL, Hown⟩
      · ipureintro
        refine ⟨Hl0, rfl, Hrevfit, fun h1 h2 => permKeysOk_putUser _ _ _ (Hpk st0 Hl0 h1 h2), ?_⟩
        intro hM; subst hM; exact Hl0
      have Hl1 := histLast_after M hs (putUser st0 user xs') rev (fun h => by subst h; exact Hl0) Hrev
      imod (authSnapF_of_last M _ _ Hl1) $$ Hown with ⟨Hown, #Hsnap⟩
      (try wp_auto)
      wp_bind (App (Val (st @!! go.GoType.PointerType authStore.ty @!! go!"refreshRangePermCache"))
        (Val #(GoInterface.ok ti)))
      iapply (h_refresh st R M ti (fun x => Lk x Post)
          ({ putUser st0 user xs' with revision := rev } : AuthState) (hs ++ [bump (putUser st0 user xs')]))
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
      wp_apply h_String _ _ as %f1 -
      (try wp_auto)
      iunfold ownUser at Huu
      icases Huu with ⟨%ums', %unm', %upw', %url', %uo', %uuf', %usc', Huu, -, -, -, -⟩
      icases typedPointsto_split _ _ _ $$ Huu with Huu
      simp only [TypedPointsto.typedPointstoDef]
      iNamed Huu
      (try wp_auto)
      wp_apply h_Strings _ _ as %f2 -
      (try wp_auto)
      wp_apply h_String _ _ as %f3 -
      (try wp_auto)
      wp_apply wp_slice_literal (V := go_uber_org.zap.zapcore.Field) [f1, f2, f3]
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
      wp_apply HUnlock $$ %_ %Post %(hs ++ [bump (putUser st0 user xs')]) [HL $Hown]
        as ⟨HPost, HT, Hown⟩
      · isplitl [HL]
        · iExactEq HL
          all_goals rfl
        ipureintro; exact Hl1
      (try wp_auto)
      iapply HΦ
      iexists b0, ({ putUser st0 user xs' with revision := rev } : AuthState)
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
      iexists st0, (.next (bump (putUser st0 user xs')))
      isplitr
      · ipureintro; exact tieStep_refresh M hs _ b0 sc0 _ st0 Hl0 Hl1 rfl
      isplitr
      · ipureintro; exact ⟨Hl0, hstepR⟩
      simp only [outRes]
      isplitl [Hown]
      · iExactEq Hown
        all_goals rfl
      · ipureintro; trivial
  )


theorem auth.authStore.UserGrantRole.wp_tie
    (h_commitRevision : auth.authStore.commitRevision.spec (GF := GF) (hG := hG))
    (h_refresh : auth.authStore.refreshRangePermCache.spec (GF := GF) (hG := hG))
    (h_String : zap.String.spec (GF := GF) (hG := hG))
    (h_Strings : zap.Strings.spec (GF := GF) (hG := hG))
    (h_Warn : zap.Logger.Warn.spec (GF := GF) (hG := hG))
    (h_Info : zap.Logger.Info.spec (GF := GF) (hG := hG)) :
    auth.authStore.UserGrantRole.specT (GF := GF) (hG := hG) :=
  auth.authStore.UserGrantRole.specT_of_TB (auth.authStore.UserGrantRole.wp_tieB h_commitRevision h_refresh h_String h_Strings h_Warn h_Info)

theorem auth.authStore.UserGrantRole.wp_proof
    (h_commitRevision : auth.authStore.commitRevision.spec (GF := GF) (hG := hG))
    (h_refresh : auth.authStore.refreshRangePermCache.spec (GF := GF) (hG := hG))
    (h_String : zap.String.spec (GF := GF) (hG := hG))
    (h_Strings : zap.Strings.spec (GF := GF) (hG := hG))
    (h_Warn : zap.Logger.Warn.spec (GF := GF) (hG := hG))
    (h_Info : zap.Logger.Info.spec (GF := GF) (hG := hG)) :
    auth.authStore.UserGrantRole.spec (GF := GF) (hG := hG) :=
  auth.authStore.UserGrantRole.spec_of_T (auth.authStore.UserGrantRole.wp_tie h_commitRevision h_refresh h_String h_Strings h_Warn h_Info)

end proof

end EtcdGrove
end Perennial
