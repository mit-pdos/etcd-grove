/-
Proof of the spec of the same name (the auth plan's S4b, 2026-10-24). Lean-first (no Rocq
counterpart). The loop over the role's permission messages keeps those not on `[key, rangeEnd)`
(both `bytes.Equal`), in order; the model's permissions are those of a known type
(`RoleRec.toRole`), so the kept ones are the model's without those on the range.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.auth.authStore__RoleRevokePermission
public import Proof.go_etcd_io.etcd.server.v3.auth.LatestTie
public import Spec.go_etcd_io.etcd.server.v3.auth.authStore__refreshRangePermCache
public import Proof.go_etcd_io.etcd.server.v3.auth.VerdictLemmas
public import Spec.go_etcd_io.etcd.server.v3.auth.authStore__commitRevision
public import Spec.go_uber_org.zap.String
public import Spec.go_uber_org.zap.Logger__Info
public import Perennial.Proof.bytes
public import Perennial.Proof.github_com.mit_pdos.perennial.goose.model.strings.Base

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.auth auth go_etcd_io.etcd.api.v3

namespace auth

/-- Whether a wire permission is kept by the revocation of `[key, rangeEnd)`. -/
def keepW (key rangeEnd : GoString) (w : PermW) : Bool :=
  !(decide (w.key = key) && decide (w.rangeEnd = rangeEnd))

/-- A prefix one longer, filtered. -/
theorem filter_take_succ' {α : Type} (l : List α) (p : α → Bool) (x : α) (n : Nat)
    (h : l[n]? = some x) :
    (l.take (n + 1)).filter p = (l.take n).filter p ++ (if p x then [x] else []) := by
  rw [List.take_add_one, h, Option.toList_some, List.filter_append]
  cases hp : p x <;> simp [hp]

/-- The kept pairs' wire permissions are the kept wire permissions. -/
theorem map_snd_filter_zip {α β : Type} (xs : List α) (bs : List β) (p : β → Bool)
    (h : xs.length = bs.length) :
    ((xs.zip bs).filter (fun x => p x.2)).map Prod.snd = bs.filter p := by
  induction xs generalizing bs with
  | nil => cases bs with
    | nil => rfl
    | cons _ _ => simp at h
  | cons a xs ih => cases bs with
    | nil => simp at h
    | cons b bs =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at h
      simp only [List.zip_cons_cons, List.filter_cons]
      cases hp : p b <;> simp [ih bs h, hp]

/-- A known type keeps the key and the range end. -/
theorem permOfWire_some_range {w : PermW} {p : Perm} (h : permOfWire w = some p) :
    p.key = w.key ∧ p.rangeEnd = w.rangeEnd := by
  unfold permOfWire at h
  split at h
  · cases h; exact ⟨rfl, rfl⟩
  · split at h
    · cases h; exact ⟨rfl, rfl⟩
    · split at h
      · cases h; exact ⟨rfl, rfl⟩
      · cases h

/-- The model's permissions of the kept wire permissions: the model's without those on the
range. -/
theorem filterMap_filter_keepW (ws : List PermW) (key rangeEnd : GoString) :
    (ws.filter (keepW key rangeEnd)).filterMap permOfWire =
      (ws.filterMap permOfWire).filter (fun p => decide ¬ permAt key rangeEnd p) := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    simp only [List.filter_cons, List.filterMap_cons]
    cases hw : permOfWire w with
    | none =>
      cases hk : keepW key rangeEnd w <;> simp [List.filterMap_cons, hw, ih]
    | some p =>
      obtain ⟨hk, hr⟩ := permOfWire_some_range hw
      have hb : keepW key rangeEnd w = !decide (permAt key rangeEnd p) := by
        unfold keepW
        by_cases h1 : w.key = key <;> by_cases h2 : w.rangeEnd = rangeEnd <;>
          simp [permAt, hk, hr, h1, h2]
      cases hk' : keepW key rangeEnd w <;> rw [hk'] at hb <;>
        simp [List.filterMap_cons, hw, ih, List.filter_cons, ← hb]

/-- No wire permission dropped: none of the model's is on the range. -/
theorem none_on_of_all_kept (ws : List PermW) (key rangeEnd : GoString)
    (h : ∀ w ∈ ws, keepW key rangeEnd w = true) :
    ∀ p ∈ ws.filterMap permOfWire, ¬ permAt key rangeEnd p := by
  intro p hp
  obtain ⟨w, hw, hpw⟩ := List.mem_filterMap.mp hp
  obtain ⟨hk, hr⟩ := permOfWire_some_range hpw
  have := h w hw
  unfold keepW at this
  unfold permAt; rw [hk, hr]
  intro ⟨h1, h2⟩
  simp [h1, h2] at this

/-- Every second component of a zip of equal lengths is in it. -/
theorem exists_mem_zip_of_mem_snd {α β : Type} (xs : List α) (bs : List β) (b : β)
    (h : xs.length = bs.length) (hb : b ∈ bs) : ∃ a, (a, b) ∈ xs.zip bs := by
  obtain ⟨i, hi, hib⟩ := List.getElem_of_mem hb
  refine ⟨xs[i]'(by omega), ?_⟩
  rw [← hib]
  apply List.mem_iff_getElem.mpr
  refine ⟨i, by simp [List.length_zip]; omega, ?_⟩
  simp

end auth

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.auth.Assumptions]

theorem auth.authStore.RoleRevokePermission.wp_tie
    (h_commitRevision : auth.authStore.commitRevision.spec (GF := GF) (hG := hG))
    (h_refresh : auth.authStore.refreshRangePermCache.spec (GF := GF) (hG := hG))
    (h_String : zap.String.spec (GF := GF) (hG := hG))
    (h_Info : zap.Logger.Info.spec (GF := GF) (hG := hG)) :
    auth.authStore.RoleRevokePermission.specT (GF := GF) (hG := hG) := by
  intro st R M P f T hs Pre Q Post r role key rangeEnd b0 sc0
  wp_start as ⟨#Hinv, #Hr, %Hrolelen, Hown, HWR, Hcs, %Hok, #Hcap⟩
  icases authErrVar_of_init .roleNotFound $$ Hpkg with ⟨%eRNF, #HeRNF⟩
  icases authErrVar_of_init .permissionNotGranted $$ Hpkg with ⟨%ePNG, #HePNG⟩
  simp only [AuthErr.var]
  ihave #Hbytes : isPkgInit (PROP := IProp GF) pkg_id.bytes $$ []
  · iPkgInit
  ihave #Hinv' := Hinv
  iunfold authInv at Hinv'
  icases Hinv' with ⟨%Hst, -, ⟨%lg, #Hlg, %Hlgnn⟩, -, -, -, -⟩
  iunfold roleRevokePermissionReqIs at Hr
  icases Hr with ⟨%Hrnn, #HRole, ⟨%ks, #HKey, #Hks⟩, ⟨%res, #HRE, #Hres⟩⟩
  iunfold authWRx at HWR
  icases HWR with ⟨⟨%be, Hbe, #Hbeok⟩, HT, Hfl, #Hev, Hca, #Hcsn⟩
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
  icases HLk' with ⟨#HLock, #HRd, -, -, #HPutR, -, -, -, #HUnlock, -, -⟩
  (try wp_auto)
  wp_bind (App (Val #(methods ti.ty go!"Lock" ti.v)) (Val #()))
  iapply HLock $$ %hs %Pre %Q %Post [$Hcs $HT $Hown]
  inext
  iintro ⟨%st0, HL, Hown, %Hl0⟩
  ihave #HRd' := HRd $$ %Post
  iunfold authReaderOk at HRd'
  icases HRd' with ⟨-, #HGR, -, -, -⟩
  (try wp_auto)
  wp_bind (App (Val #(methods ti.ty go!"UnsafeGetRole" ti.v)) (Val #role))
  iapply HGR $$ %st0 %role HL
  inext
  iintro %rp ⟨HL, Hrole⟩
  (try wp_auto)
  wp_if_destruct
  · -- no such role
    ihave %Hnone := roleOut_null st0 role $$ Hrole
    wp_apply HUnlock $$ %st0 %Post %hs [$HL $Hown] as ⟨HPost, HT, Hown⟩
    · ipureintro; exact Hl0
    (try wp_auto)
    iapply HΦ
    iexists b0, sc0
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
    iexists st0, (.err .roleNotFound)
    isplitr
    · ipureintro; exact tieStep_same _ _ _ _
    isplitr
    · ipureintro
      refine ⟨Hl0, ?_⟩
      simp [roleRevokePermissionR, Hnone]
    simp only [outRes, authErrOf, AuthErr.var]
    iframe Hown
    iexists eRNF; iframe HeRNF; ipureintro; rfl
  ihave Hrole' := roleOut_some _ st0 role Hif $$ Hrole
  icases Hrole' with ⟨%ps, %rr, %Hrr, Hrole⟩
  obtain ⟨Hlook, Hrrn, Hrrps⟩ := Hrr
  iunfold ownRole at Hrole
  icases Hrole with ⟨%rms, %rnm, %rkp, %pps, %ruf, %rsc, Hrp, #Hrnm, #Hrkp, %Hplen, #Hperms⟩
  icases typedPointsto_split _ _ _ $$ Hrp with Hrp
  simp only [TypedPointsto.typedPointstoDef]
  iNamed Hrp
  (try wp_auto)
  obtain ⟨uu, huu⟩ : ∃ uu, uu = «$r0_ptr» := ⟨_, rfl⟩
  subst huu
  irename «$r0» => Huu
  irename «as» => Has
  (try (irename : (iprop("_" ∷ True) : IProp GF) => Hjunk; iclear Hjunk))
  ihave %Hkl := ownSlice_len _ _ _ $$ Hrkp
  let rrec : GoSlice → authpb.Role := fun sl =>
    { state' := zeroValDef, Name' := rnm, KeyPermission' := sl, unknownFields' := slice.nil,
      sizeCache' := 0 }
  let keepP : Loc × PermW → Bool := fun x => auth.keepW key rangeEnd x.2
  -- the permissions loop: the updated role holds the pairs kept so far
  ihave IH : iprop(∃ (n : w64) (pv : Loc) (sl : GoSlice),
      "i" ∷ i_ptr ↦ n ∗
      "perm" ∷ perm_ptr ↦ pv ∗
      "Huu" ∷ uu ↦ rrec sl ∗
      "Hsl" ∷ sl ↦* ((((pps.zip rr.perms).take (sint.nat n)).filter keepP).map Prod.fst) ∗
      "Hslc" ∷ ownSliceCap Loc sl (DFrac.own 1) ∗
      "#Hkept" ∷ ([∗list] x ∈ ((pps.zip rr.perms).take (sint.nat n)).filter keepP,
        ownPermW x.1 x.2) ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.nat n ≤ pps.length⌝)
    $$ [i perm Huu]
  · iexists W64 0, _, slice.nil
    iframe
    rw [show List.take (sint.nat (W64 0)) (pps.zip rr.perms) = [] from rfl, List.filter_nil,
      List.map_nil]
    isplitl []
    · iapply ownSlice_nil
    isplitl []
    · iapply ownSliceCap_nil
    isplitl []
    · iapply BigSepL.bigSepL_nil.2; itrivial
    ipureintro; word
  wp_for IH
  wp_if_destruct
  · -- another permission
    have hlt : sint.Z n < sint.Z rkp.len := by
      first | exact Hif | exact of_decide_eq_true (go.intoVal_inj Hif)
    have hn : sint.nat n < pps.length := by rw [Hkl.1]; word
    obtain ⟨pp, hpp⟩ : ∃ x, pps[sint.nat n]? = some x := ⟨_, List.getElem?_eq_getElem hn⟩
    obtain ⟨w, hw⟩ : ∃ x, rr.perms[sint.nat n]? = some x :=
      ⟨_, List.getElem?_eq_getElem (by rw [← Hplen]; exact hn)⟩
    have hz : (pps.zip rr.perms)[sint.nat n]? = some (pp, w) := by
      rw [List.getElem?_zip_eq_some]; exact ⟨hpp, hw⟩
    have Hbnd : 0 ≤ sint.Z n ∧ sint.Z n < sint.Z rkp.len := ⟨Hn.1, hlt⟩
    (try wp_auto)
    simp only [Hbnd, _root_.and_self, ↓reduceIte]
    wp_apply wp_load_slice_index rkp (sint.Z n) pps .discard pp Hn.1 $$ [$Hrkp] as -
    · iframe; ipureintro; exact hpp
    ihave #Hpw := BigSepL.bigSepL_lookup (Φ := fun (_ : Nat) (x : Loc × PermW) =>
      ownPermW (GF := GF) x.1 x.2) (l := pps.zip rr.perms) (i := sint.nat n) (x := (pp, w)) hz
      $$ Hperms
    ihave #Hpw2 := Hpw
    iunfold ownPermW at Hpw2
    icases Hpw2 with ⟨%Hppnn, %pms, %kk, %kre, %puf, %psc, #Hpp, #Hkk, #Hkre⟩
    icases typedPointsto_split _ _ _ $$ Hpp with Hpp
    simp only [TypedPointsto.typedPointstoDef]
    iNamed Hpp
    (try wp_auto)
    have hsucc : sint.nat (n + W64 1) = sint.nat n + 1 := by word
    wp_apply (_root_.Perennial.bytes.wp_Equal kk ks DFrac.discard DFrac.discard w.key key)
      $$ [$Hkk $Hks] as ⟨-, -⟩
    (try wp_auto)
    -- the step's three cases: kept unless both the key and the range end match
    have hkeep_iff : keepP (pp, w) = true ↔ ¬ (w.key = key ∧ w.rangeEnd = rangeEnd) := by
      show (!(decide (w.key = key) && decide (w.rangeEnd = rangeEnd))) = true ↔ _
      by_cases h1 : w.key = key <;> by_cases h2 : w.rangeEnd = rangeEnd <;> simp [h1, h2]
    wp_if_destruct
    · -- the key matches: the range end decides
      wp_apply (_root_.Perennial.bytes.wp_Equal kre res DFrac.discard DFrac.discard w.rangeEnd rangeEnd)
        $$ [$Hkre $Hres] as ⟨-, -⟩
      (try wp_auto)
      wp_if_destruct
      · -- both match: dropped
        (try wp_auto)
        have hk : keepP (pp, w) = false := by
          cases h : keepP (pp, w)
          · rfl
          · exact absurd (hkeep_iff.mp h) (by simp)
        have hstep' : ((pps.zip rr.perms).take (sint.nat n + 1)).filter keepP =
            ((pps.zip rr.perms).take (sint.nat n)).filter keepP := by
          rw [auth.filter_take_succ' _ _ _ _ hz]; simp [hk]
        wp_for_post
        iframe
        iexists n + W64 1, pp, sl
        iframe
        isplitl [Hsl]
        · rw [hsucc, hstep']; iexact Hsl
        isplitl []
        · rw [hsucc, hstep']; iexact Hkept
        ipureintro; constructor <;> word
      · -- the range end differs: kept
        (try wp_auto)
        wp_apply wp_slice_literal (V := Loc) [pp]
        isplitr
        · ipureintro; rfl
        iintro %xs ⟨Hxs, -⟩
        (try wp_auto)
        wp_apply wp_slice_append sl _ _ [pp] (DFrac.own 1) $$ [$Hsl $Hslc $Hxs] as %sl' ⟨Hsl, Hslc, -⟩
        (try wp_auto)
        have hk : keepP (pp, w) = true := hkeep_iff.mpr (by intro h; exact Hif h.2)
        have hstep' : ((pps.zip rr.perms).take (sint.nat n + 1)).filter keepP =
            ((pps.zip rr.perms).take (sint.nat n)).filter keepP ++ [(pp, w)] := by
          rw [auth.filter_take_succ' _ _ _ _ hz, if_pos hk]
        wp_for_post
        iframe
        iexists n + W64 1, pp, sl'
        iframe
        isplitl [Hsl]
        · iExactEq Hsl
          all_goals (rw [hsucc, hstep', List.map_append]; rfl)
        isplitl []
        · rw [hsucc, hstep']; iapply BigSepL.bigSepL_snoc.2; iframe Hkept Hpw
        ipureintro; constructor <;> word
    · -- the key differs: kept
      (try wp_auto)
      wp_apply wp_slice_literal (V := Loc) [pp]
      isplitr
      · ipureintro; rfl
      iintro %xs ⟨Hxs, -⟩
      (try wp_auto)
      wp_apply wp_slice_append sl _ _ [pp] (DFrac.own 1) $$ [$Hsl $Hslc $Hxs] as %sl' ⟨Hsl, Hslc, -⟩
      (try wp_auto)
      have hk : keepP (pp, w) = true := hkeep_iff.mpr (by intro h; exact Hif h.1)
      have hstep' : ((pps.zip rr.perms).take (sint.nat n + 1)).filter keepP =
          ((pps.zip rr.perms).take (sint.nat n)).filter keepP ++ [(pp, w)] := by
        rw [auth.filter_take_succ' _ _ _ _ hz, if_pos hk]
      wp_for_post
      iframe
      iexists n + W64 1, pp, sl'
      iframe
      isplitl [Hsl]
      · iExactEq Hsl
        all_goals (rw [hsucc, hstep', List.map_append]; rfl)
      isplitl []
      · rw [hsucc, hstep']; iapply BigSepL.bigSepL_snoc.2; iframe Hkept Hpw
      ipureintro; constructor <;> word
  -- the loop is over: every permission seen
  have hzl : (pps.zip rr.perms).length = pps.length := by
    rw [List.length_zip, ← Hplen, Nat.min_self]
  have hall : sint.nat n = pps.length := by
    have := Hkl.1; word
  rw [hall, ← hzl, List.take_length] at *
  obtain ⟨kept, hkept⟩ : ∃ l, l = (pps.zip rr.perms).filter keepP := ⟨_, rfl⟩
  ihave Hsl : sl ↦* kept.map Prod.fst $$ [Hsl]
  · rw [hkept]; iexact Hsl
  ihave #Hkept : [∗list] x ∈ kept, ownPermW x.1 x.2 $$ []
  · rw [hkept]; iexact Hkept
  ihave %Hsll := ownSlice_len _ _ _ $$ Hsl
  have hsnd : kept.map Prod.snd = rr.perms.filter (auth.keepW key rangeEnd) := by
    rw [hkept]; exact auth.map_snd_filter_zip pps rr.perms (auth.keepW key rangeEnd) Hplen
  (try wp_auto)
  wp_if_destruct
  · -- nothing revoked: `ErrPermissionNotGranted`
    have hlen : kept.length = pps.length := by
      have h1 := Hsll.1; have h2 := Hkl.1
      first | (rw [List.length_map] at h1; word) | omega
    have hallk : ∀ w ∈ rr.perms, auth.keepW key rangeEnd w = true := by
      have hl2 : (rr.perms.filter (auth.keepW key rangeEnd)).length = rr.perms.length := by
        rw [← hsnd, List.length_map, hlen, Hplen]
      exact List.length_filter_eq_length_iff.mp hl2
    have hnone : ∀ p ∈ ps, ¬ permAt key rangeEnd p := by
      intro p hp
      exact auth.none_on_of_all_kept rr.perms key rangeEnd hallk p (Hrrps.symm.subset hp)
    wp_apply HUnlock $$ %st0 %Post %hs [$HL $Hown] as ⟨HPost, HT, Hown⟩
    · ipureintro; exact Hl0
    (try wp_auto)
    iapply HΦ
    iexists b0, sc0
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
    iexists st0, (.err .permissionNotGranted)
    isplitr
    · ipureintro; exact tieStep_same _ _ _ _
    isplitr
    · ipureintro
      refine ⟨Hl0, ?_⟩
      simp only [roleRevokePermissionR, Hlook]
      first | exact Or.inl ⟨rfl, hnone⟩ | exact Or.inl ⟨trivial, hnone⟩
    simp only [outRes, authErrOf, AuthErr.var]
    iframe Hown
    iexists ePNG; iframe HePNG; ipureintro; rfl
  -- some permission revoked: the role put
  let rr' : RoleRec := { name := rr.name, perms := kept.map Prod.snd }
  have hps' : rr'.toRole.Perm (ps.filter (fun p => ¬ permAt key rangeEnd p)) := by
    show ((kept.map Prod.snd).filterMap permOfWire).Perm _
    rw [hsnd, auth.filterMap_filter_keepW]; exact Hrrps.filter _
  imod (ownSlice_persist _ _ _) $$ Hsl with #Hsl'
  wp_bind (App (Val #(methods ti.ty go!"UnsafePutRole" ti.v)) (Val #uu))
  iapply HPutR $$ %st0 %Post %uu %rr' %(ps.filter (fun p => ¬ permAt key rangeEnd p)) [HL Huu]
  · iframe HL
    isplitl [Huu]
    · iunfold ownRole
      iexists zeroValDef, rnm, sl, kept.map Prod.fst, slice.nil, (0 : w32)
      iframe Huu Hrnm Hsl'
      isplitr
      · ipureintro; simp [rr']
      have hz : (kept.map Prod.fst).zip rr'.perms = kept := by
        show (kept.map Prod.fst).zip (kept.map Prod.snd) = kept
        rw [← List.unzip_fst, ← List.unzip_snd, List.zip_unzip]
      rw [hz]; iexact Hkept
    ipureintro; exact ⟨show rr.name.length ≤ _ by rw [Hrrn]; exact Hrolelen, hps'⟩
  inext
  iintro ⟨HL, Huu⟩
  (try wp_auto)
  obtain ⟨ps', hps'eq⟩ : ∃ l, l = ps.filter (fun p => ¬ permAt key rangeEnd p) := ⟨_, rfl⟩
  ihave HL : Lk (putRole st0 role ps') Post $$ [HL]
  · iExactEq HL; show Lk (putRole st0 rr.name _) Post = _; rw [Hrrn, hps'eq]
  ihave %Hpk := authOwnF_last_permKeysOk M hs $$ Hown
  have hstep : roleRevokePermissionR role key rangeEnd st0 (.next (bump (putRole st0 role ps'))) := by
    simp only [roleRevokePermissionR, Hlook]
    right; rw [hps'eq]
  obtain ⟨Hrevfit, Hfit⟩ := Hok st0 Hl0
  have Hfit' := Hfit _ _ hstep rfl
  ihave #Hcn := capNextM_use M hs _ st0 (bump (putRole st0 role ps')) Hl0 hstep $$ Hcap
  wp_apply (h_commitRevision st R M P f T ti Lk (putRole st0 role ps') Post hs st0)
    $$ [$Hinv $HLk $HL $Hown $Hcn] as ⟨%rev, %Hrev, HL, Hown⟩
  · ipureintro
    refine ⟨Hl0, rfl, Hrevfit, fun h1 h2 => permKeysOk_putRole _ _ _ (Hpk st0 Hl0 h1 h2)
      (fun p hp => Hpk st0 Hl0 h1 h2 role ps Hlook p (by rw [hps'eq] at hp; exact (List.mem_filter.mp hp).1)), ?_⟩
    intro hM; subst hM; exact Hl0
  have Hl1 := histLast_after M hs (putRole st0 role ps') rev (fun h => by subst h; exact Hl0) Hrev
  imod (authSnapF_of_last M _ _ Hl1) $$ Hown with ⟨Hown, #Hsnap⟩
  (try wp_auto)
  wp_bind (App (Val (st @!! go.GoType.PointerType authStore.ty @!! go!"refreshRangePermCache"))
    (Val #(GoInterface.ok ti)))
  iapply (h_refresh st R M ti (fun x => Lk x Post)
      ({ putRole st0 role ps' with revision := rev } : AuthState) (hs ++ [bump (putRole st0 role ps')]))
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
  wp_apply (wp_bytes_to_string ks key DFrac.discard) $$ [$Hks] as -
  (try wp_auto)
  wp_apply h_String _ _ as %f2 -
  (try wp_auto)
  wp_apply (wp_bytes_to_string res rangeEnd DFrac.discard) $$ [$Hres] as -
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
  wp_apply HUnlock $$ %_ %Post %(hs ++ [bump (putRole st0 role ps')]) [HL $Hown]
    as ⟨HPost, HT, Hown⟩
  · isplitl [HL]
    · iExactEq HL
      all_goals rfl
    ipureintro; exact Hl1
  (try wp_auto)
  iapply HΦ
  iexists b0, ({ putRole st0 role ps' with revision := rev } : AuthState)
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
  iexists st0, (.next (bump (putRole st0 role ps')))
  isplitr
  · ipureintro; exact tieStep_refresh M hs _ b0 sc0 _ st0 Hl0 Hl1 rfl
  isplitr
  · ipureintro; exact ⟨Hl0, hstep⟩
  simp only [outRes]
  isplitl [Hown]
  · iExactEq Hown
    all_goals rfl
  · ipureintro; trivial


theorem auth.authStore.RoleRevokePermission.wp_proof
    (h_commitRevision : auth.authStore.commitRevision.spec (GF := GF) (hG := hG))
    (h_refresh : auth.authStore.refreshRangePermCache.spec (GF := GF) (hG := hG))
    (h_String : zap.String.spec (GF := GF) (hG := hG))
    (h_Info : zap.Logger.Info.spec (GF := GF) (hG := hG)) :
    auth.authStore.RoleRevokePermission.spec (GF := GF) (hG := hG) :=
  auth.authStore.RoleRevokePermission.spec_of_T (auth.authStore.RoleRevokePermission.wp_tie h_commitRevision h_refresh h_String h_Info)

end proof

end EtcdGrove
end Perennial
