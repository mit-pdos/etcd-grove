/-
Proof of the spec of the same name (the auth plan's S4b, 2026-10-24). Lean-first (no Rocq
counterpart). After the role's deletion, the loop over the state's users (`UnsafeGetAllUsers`:
each user once) puts back every user who had the role, without it (the inner loop is
`UserRevokeRole`'s); a user without it is left (`continue`). After the k-th user the state's users
are the first k names' roles filtered, the others' as they were: at the end, the model's `delRole`.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.auth.authStore__RoleDelete
public import Proof.go_etcd_io.etcd.server.v3.auth.LatestTie
public import Spec.go_etcd_io.etcd.server.v3.auth.authStore__refreshRangePermCache
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

namespace auth

/-- The users after the first `k` of `names` were revoked `role`. -/
def usersAfter (us : GMap GoString User) (names : List GoString) (k : Nat) (role : GoString)
    (u' : GMap GoString User) : Prop :=
  ∀ n, u' !! n = if n ∈ names.take k then (us !! n).map (fun u => u.filter fun r => r ≠ role)
    else us !! n

theorem usersAfter_zero (us : GMap GoString User) (names : List GoString) (role : GoString) :
    usersAfter us names 0 role us := by
  intro n; simp

/-- The k-th user left unchanged (without the role). -/
theorem usersAfter_succ_same (us u' : GMap GoString User) (names : List GoString) (k : Nat)
    (role nm : GoString) (roles : User) (hnm : names[k]? = some nm) (hus : us !! nm = some roles)
    (hno : role ∉ roles) (h : usersAfter us names k role u') :
    usersAfter us names (k + 1) role u' := by
  intro n
  rw [h n, List.take_add_one, hnm, Option.toList_some]
  by_cases hn : n = nm
  · subst hn
    have hf : roles.filter (fun r => decide (r ≠ role)) = roles :=
      List.filter_eq_self.mpr (fun r hr => by
        have : r ≠ role := fun he => hno (he ▸ hr)
        simpa using this)
    have hf' : roles.filter (fun r => !decide (r = role)) = roles := by simpa using hf
    simp [hus, hf']
  · simp [List.mem_append, hn]

/-- The k-th user put back without the role. -/
theorem usersAfter_succ_put (us u' : GMap GoString User) (names : List GoString) (k : Nat)
    (role nm : GoString) (roles : User) (hnm : names[k]? = some nm) (hus : us !! nm = some roles)
    (h : usersAfter us names k role u') :
    usersAfter us names (k + 1) role
      (GMap.insert nm (roles.filter fun r => r ≠ role) u') := by
  intro n
  rw [List.take_add_one, hnm, Option.toList_some]
  by_cases hn : nm = n
  · subst hn
    simp [GMap.lookup_insert, hus]
  · rw [GMap.lookup_insert_ne _ _ hn, h n]
    have : n ≠ nm := fun he => hn he.symm
    simp [List.mem_append, this]

/-- All users seen: the model's users without the role. -/
theorem usersAfter_all (us u' : GMap GoString User) (names : List GoString) (role : GoString)
    (hmem : ∀ n, n ∈ names ↔ (us !! n).isSome) (h : usersAfter us names names.length role u') :
    u' = GMap.fmap (fun u => u.filter fun r => r ≠ role) us := by
  apply GMap.ext
  intro n
  have := h n
  rw [List.take_length] at this
  show u' !! n = _
  rw [this, GMap.lookup_fmap]
  by_cases hn : n ∈ names
  · simp [hn]
  · have : us !! n = none := by
      cases h' : us !! n with
      | none => rfl
      | some _ => exact absurd ((hmem n).mpr (by simp [h'])) hn
    simp [hn, this]

end auth

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.auth.Assumptions]

theorem auth.authStore.RoleDelete.wp_tie
    (h_commitRevision : auth.authStore.commitRevision.spec (GF := GF) (hG := hG))
    (h_refresh : auth.authStore.refreshRangePermCache.spec (GF := GF) (hG := hG))
    (h_String : zap.String.spec (GF := GF) (hG := hG))
    (h_Error : zap.Logger.Error.spec (GF := GF) (hG := hG))
    (h_Info : zap.Logger.Info.spec (GF := GF) (hG := hG)) :
    auth.authStore.RoleDelete.specT (GF := GF) (hG := hG) := by
  intro st R M P f T hs Pre Q Post r role en sc0
  wp_start as ⟨#Hinv, #Hr, Hown, HWR, Hcs, %Hok, %Hnames⟩
  icases authErrVar_of_init .roleNotFound $$ Hpkg with ⟨%eRNF, #HeRNF⟩
  icases authErrVar_of_init .invalidAuthMgmt $$ Hpkg with ⟨%eIAM, #HeIAM⟩
  simp only [AuthErr.var]
  ihave #Hinv' := Hinv
  iunfold authInv at Hinv'
  icases Hinv' with ⟨%Hst, -, ⟨%lg, #Hlg, %Hlgnn⟩, -, ⟨%tp, #Htp, #Htpok⟩, -, -⟩
  iunfold tokenProviderOk at Htpok
  icases Htpok with ⟨%Atp, %tpi, %Htpi, -, -, -, #HInval, -⟩
  subst Htpi
  iunfold roleDeleteReqIs at Hr
  icases Hr with ⟨%Hrnn, #HN⟩
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
  wp_join (Q := fun v => iprop(⌜v = #(decide (en = true ∧ role = go!"root"))⌝ ∗
      auth.aF go!"enabled" st ↦{DFrac.own (1 : Qp).half} en ∗ r_ptr ↦ r ∗ as_ptr ↦ st))
    at (if: _ then _ else #false) with [Hen r «as»] as ⟨%Hv, Hen, r, «as»⟩
  · cases en
    · (try wp_auto)
      iframe
      ipureintro; simp
    · (try wp_auto)
      iframe
      ipureintro; simp
  subst Hv
  wp_if_destruct
  · -- `root` with auth enabled: refused
    obtain ⟨Hen1, Hroot⟩ := Hif
    subst Hen1
    (try wp_auto)
    wp_apply h_String _ _ as %f1 -
    (try wp_auto)
    wp_apply wp_slice_literal (V := go_uber_org.zap.zapcore.Field) [f1]
    isplitr
    · ipureintro; rfl
    iintro %fsl ⟨-, -⟩
    (try wp_auto)
    wp_apply h_Error
    · ipureintro; exact Hlgnn
    (try wp_auto)
    iapply HΦ
    iexists true, sc0
    isplitl [Hcs]
    · iapply csContract_noWrite $$ Hcs
    isplitl [Hbe HT Hen HenQ Hca]
    · iunfold authWRx; iunfold flagAt; iframe HT Hen HenQ Hev Hca Hcsn; iexists (GoInterface.ok bi); iframe Hbe Hbeok
    isplitr
    · iunfold respOk; isplitr
      · ipureintro; intro _; rfl
      · ileft; ipureintro; rfl
    iexists true
    iframe Hev
    iunfold adminOutP
    iright
    ihave %Hl := authOwn_exists_last M hs $$ Hown
    obtain ⟨st0, Hl⟩ := Hl
    iexists st0, (.err .invalidAuthMgmt)
    isplitr
    · ipureintro; exact tieStep_same _ _ _ _
    isplitr
    · ipureintro
      refine ⟨Hl, ?_⟩
      simp [stepOf, roleDeleteF, rootRole, Hroot]
    simp only [outRes]
    iframe Hown
    simp only [authErrOf, AuthErr.var]; iexists eIAM; iframe HeIAM; ipureintro; rfl
  have hnr : ¬ (en = true ∧ role = rootRole) := Hif
  clear Hif
  wp_apply HBatch as %tx Htx
  iunfold authBatchTxOk at Htx
  icases Htx with ⟨%ti, %Hti, %Lk, #HLk⟩
  subst Hti
  ihave #HLk' := HLk
  iunfold authBatchTxLk at HLk'
  icases HLk' with ⟨#HLock, #HRd, #HPutU, -, -, #HDelR, -, -, #HUnlock, -, -⟩
  (try wp_auto)
  wp_bind (App (Val #(methods ti.ty go!"Lock" ti.v)) (Val #()))
  iapply HLock $$ %hs %Pre %Q %Post [$Hcs $HT $Hown]
  inext
  iintro ⟨%st0, HL, Hown, %Hl0⟩
  ihave #HRd' := HRd $$ %Post
  iunfold authReaderOk at HRd'
  icases HRd' with ⟨-, #HGR, -, -, #HGA⟩
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
    iexists en, sc0
    isplitl [HPost]
    · ileft; iexact HPost
    isplitl [Hbe HT Hen HenQ Hca]
    · iunfold authWRx; iunfold flagAt; iframe HT Hen HenQ Hev Hca Hcsn; iexists (GoInterface.ok bi); iframe Hbe Hbeok
    isplitr
    · iunfold respOk; isplitr
      · ipureintro; intro _; rfl
      · ileft; ipureintro; rfl
    iexists en
    iframe Hev
    iunfold adminOutP
    iright
    iexists st0, (.err .roleNotFound)
    isplitr
    · ipureintro; exact tieStep_same _ _ _ _
    isplitr
    · ipureintro
      refine ⟨Hl0, ?_⟩
      simp [stepOf, roleDeleteF, hnr, Hnone]
    simp only [outRes, authErrOf, AuthErr.var]
    iframe Hown
    iexists eRNF; iframe HeRNF; ipureintro; rfl
  ihave Hrole' := roleOut_some _ st0 role Hif $$ Hrole
  icases Hrole' with ⟨%ps, %rr, %Hrr, -⟩
  wp_bind (App (Val #(methods ti.ty go!"UnsafeDeleteRole" ti.v)) (Val #role))
  iapply HDelR $$ %st0 %Post %role HL
  inext
  iintro HL
  (try wp_auto)
  obtain ⟨st1, hst1⟩ : ∃ s, s = ({ st0 with roles := GMap.delete role st0.roles } : AuthState) :=
    ⟨_, rfl⟩
  ihave HL : Lk st1 Post $$ [HL]
  · rw [hst1]; iexact HL
  wp_bind (App (Val #(methods ti.ty go!"UnsafeGetAllUsers" ti.v)) (Val #()))
  iapply HGA $$ %st1 HL
  inext
  iintro %s %us %names ⟨HL, Hs, %Hus, Husers⟩
  (try wp_auto)
  obtain ⟨Huslen, Hnodup, Hmem⟩ := Hus
  irename «as» => Has
  obtain ⟨io, hio⟩ : ∃ io, io = i_ptr := ⟨_, rfl⟩
  subst hio
  -- the users loop: the first k users revoked the role
  ihave IHo : iprop(∃ (k : w64) (uv : Loc) (sk : AuthState),
      "i" ∷ io ↦ k ∗
      "user" ∷ user_ptr ↦ uv ∗
      "HL" ∷ Lk sk Post ∗
      "Hs" ∷ s ↦* us ∗
      "Husers" ∷ ([∗list] x ∈ (us.zip names).drop (sint.nat k), userOut x.1 st1 x.2) ∗
      "%Hk" ∷ ⌜0 ≤ sint.Z k ∧ sint.nat k ≤ us.length ∧ sk.enabled = st1.enabled ∧
        sk.revision = st1.revision ∧ sk.roles = st1.roles ∧
        auth.usersAfter st1.users names (sint.nat k) role sk.users⌝)
    $$ [i user HL Hs Husers]
  · iexists W64 0, _, st1
    iframe
    ipureintro
    exact ⟨by word, by word, rfl, rfl, rfl, auth.usersAfter_zero _ _ _⟩
  wp_for IHo
  wp_if_destruct
  · -- another user
    have hlt : sint.Z k < sint.Z s.len := by
      first | exact Hif | exact of_decide_eq_true (go.intoVal_inj Hif)
    ihave %Hsl := ownSlice_len _ _ _ $$ Hs
    have hk : sint.nat k < us.length := by rw [Hsl.1]; word
    have hkz : sint.nat k < (us.zip names).length := by
      rw [List.length_zip, ← Huslen, Nat.min_self]; exact hk
    obtain ⟨u, hu⟩ : ∃ x, us[sint.nat k]? = some x := ⟨_, List.getElem?_eq_getElem hk⟩
    obtain ⟨nm, hnm⟩ : ∃ x, names[sint.nat k]? = some x :=
      ⟨_, List.getElem?_eq_getElem (by rw [← Huslen]; exact hk)⟩
    have hz : (us.zip names)[sint.nat k]'hkz = (u, nm) := by
      have : (us.zip names)[sint.nat k]? = some (u, nm) := by
        rw [List.getElem?_zip_eq_some]; exact ⟨hu, hnm⟩
      rw [List.getElem?_eq_getElem hkz, Option.some.injEq] at this; exact this
    rw [List.drop_eq_getElem_cons hkz, hz]
    irename i => Hio
    icases BigSepL.bigSepL_cons.1 $$ Husers with ⟨Hu, Husers⟩
    have Hbnd : 0 ≤ sint.Z k ∧ sint.Z k < sint.Z s.len := ⟨Hk.1, hlt⟩
    (try wp_auto)
    simp only [Hbnd, _root_.and_self, ↓reduceIte]
    wp_apply wp_load_slice_index s (sint.Z k) us (DFrac.own 1) u Hk.1 $$ [$Hs] as Hs
    · iframe; ipureintro; exact hu
    (try wp_auto)
    have hnmmem : nm ∈ names := List.mem_of_getElem? hnm
    obtain ⟨roles, hlook⟩ : ∃ roles, st1.users !! nm = some roles := by
      cases h : st1.users !! nm with
      | none => have := (Hmem nm).mp hnmmem; simp [h] at this
      | some r => exact ⟨r, rfl⟩
    have hlook' : st1.users.lookup nm = some roles := hlook
    iunfold userOut at Hu
    simp only [hlook']
    icases Hu with ⟨%ur, %Hur, Hu⟩
    obtain ⟨Hurn, Hurr, Hsorted⟩ := Hur
    iunfold ownUser at Hu
    icases Hu with ⟨%ums, %unm, %upw, %url, %uo, %uuf, %usc, Hup, #Hunm, #Hupw, #Hurl, #Huo⟩
    icases typedPointsto_split _ _ _ $$ Hup with Hup
    simp only [TypedPointsto.typedPointstoDef]
    iNamed Hup
    (try wp_auto)
    obtain ⟨uu, huu⟩ : ∃ uu, uu = «$r0_ptr» := ⟨_, rfl⟩
    subst huu
    irename «$r0» => Huu
    (try (irename : (iprop("_" ∷ True) : IProp GF) => Hjunk; iclear Hjunk))
    ihave %Hrl := ownSlice_len _ _ _ $$ Hurl
    let urec : GoSlice → authpb.User := fun sl =>
      { state' := zeroValDef, Name' := unm, Password' := upw, Roles' := sl, Options' := uo,
        unknownFields' := slice.nil, sizeCache' := 0 }
    -- the roles loop (`UserRevokeRole`'s)
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
      · iapply (show ⊢ (slice.nil ↦* ((ur.roles.take (sint.nat (W64 0))).filter
            (fun r => decide (r ≠ role))) : IProp GF) from by
          rw [show List.take (sint.nat (W64 0)) ur.roles = [] from rfl, List.filter_nil]
          exact ownSlice_nil _)
      isplitl []
      · iapply ownSliceCap_nil
      ipureintro; word
    wp_for IH
    wp_if_destruct
    · -- another role
      have hlt2 : sint.Z n < sint.Z url.len := by
        first | exact Hif | exact of_decide_eq_true (go.intoVal_inj Hif)
      have hn : sint.nat n < ur.roles.length := by rw [Hrl.1]; word
      obtain ⟨x, hx⟩ : ∃ x, ur.roles[sint.nat n]? = some x := ⟨_, List.getElem?_eq_getElem hn⟩
      have Hbnd2 : 0 ≤ sint.Z n ∧ sint.Z n < sint.Z url.len := ⟨Hn.1, hlt2⟩
      (try wp_auto)
      simp only [Hbnd2, _root_.and_self, ↓reduceIte]
      wp_apply wp_load_slice_index url (sint.Z n) ur.roles .discard x Hn.1 $$ [$Hurl] as -
      · iframe; ipureintro; exact hx
      (try wp_auto)
      have hsucc : sint.nat (n + W64 1) = sint.nat n + 1 := by word
      wp_if_destruct
      · -- the deleted role: skipped
        (try wp_auto)
        wp_for_post
        iframe
        iexists n + W64 1, x, sl
        iframe
        isplitl [Hsl]
        · have hx' : ¬ (x ≠ role) := by
            first | exact fun h => h Hif | (intro h; exact h (by simpa using Hif)) | simpa using Hif
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
    -- the roles loop is over
    have hall : sint.nat n = ur.roles.length := by
      have : ¬ sint.Z n < sint.Z url.len := by
        first | exact Hif | (intro h; apply Hif; simp [h])
      rw [Hrl.1]; word
    rw [hall, List.take_length] at *
    obtain ⟨roles', hroles'⟩ : ∃ l, l = ur.roles.filter (fun r => decide (r ≠ role)) := ⟨_, rfl⟩
    ihave Hsl : sl ↦* roles' $$ [Hsl]
    · rw [hroles']; iexact Hsl
    ihave %Hsll := ownSlice_len _ _ _ $$ Hsl
    have hlen_iff := auth.filter_ne_length_eq_iff ur.roles role
    rw [← hroles'] at hlen_iff
    have hksucc : sint.nat (k + W64 1) = sint.nat k + 1 := by word
    simp only [urec]
    (try wp_auto)
    by_cases Hif : sl.len = url.len
    · -- the user did not have the role: left
      simp only [Hif, _root_.decide_true]
      have hnot : role ∉ ur.roles := by
        apply hlen_iff.mp
        have h1 := Hsll.1; have h2 := Hrl.1
        rw [h1, h2, Hif]
      (try wp_auto)
      wp_for_post
      iframe
      iexists k + W64 1, u, sk
      iframe
      isplitl [Husers]
      · rw [hksucc]; iexact Husers
      ipureintro
      refine ⟨by word, by word, Hk.2.2.1, Hk.2.2.2.1, Hk.2.2.2.2.1, ?_⟩
      rw [hksucc]
      exact auth.usersAfter_succ_same _ _ _ _ _ _ roles hnm hlook (Hurr ▸ hnot) Hk.2.2.2.2.2
    -- the user had the role: put back without it
    simp only [Hif, decide_false]
    (try wp_auto)
    imod (ownSlice_persist _ _ _) $$ Hsl with #Hsl'
    have hsorted' : roles'.Pairwise go.GoStringLt := by
      rw [hroles']; exact (Hurr ▸ Hsorted).filter _
    have hlook0 : st0.users !! nm = some roles := by rw [hst1] at hlook; exact hlook
    have hnmlen : nm.length ≤ backend.maxKeySize := Hnames st0 Hl0 nm (by simp [hlook0])
    wp_bind (App (Val #(methods ti.ty go!"UnsafePutUser" ti.v)) (Val #uu))
    iapply HPutU $$ %sk %Post %uu
      %({ name := ur.name, password := ur.password, roles := roles', noPassword := ur.noPassword } : UserRec)
      [HL Huu]
    · iframe HL
      isplitl [Huu]
      · iunfold ownUser
        iexists zeroValDef, unm, upw, sl, uo, slice.nil, (0 : w32)
        iframe Huu Hunm Hupw Hsl' Huo
      ipureintro; exact ⟨hsorted', by rw [Hurn]; exact hnmlen⟩
    inext
    iintro ⟨HL, -⟩
    (try wp_auto)
    wp_for_post
    iframe
    iexists k + W64 1, u, (putUser sk nm roles')
    iframe
    isplitl [HL]
    · iExactEq HL; rw [Hurn]
    isplitl [Husers]
    · rw [hksucc]; iexact Husers
    ipureintro
    refine ⟨by word, by word, Hk.2.2.1, Hk.2.2.2.1, Hk.2.2.2.2.1, ?_⟩
    rw [hksucc, hroles']
    exact auth.usersAfter_succ_put _ _ _ _ _ _ roles hnm hlook Hk.2.2.2.2.2 |> fun h => by
      rw [Hurr] at *; exact h
  -- the users loop is over: every user revoked the role
  ihave %Hsl := ownSlice_len _ _ _ $$ Hs
  have hkall : sint.nat k = names.length := by
    have : ¬ sint.Z k < sint.Z s.len := by
      first | exact Hif | (intro h; apply Hif; simp [h])
    rw [← Huslen, Hsl.1]; word
  obtain ⟨Hk0, -, Hken, Hkrev, Hkroles, Hkusers⟩ := Hk
  rw [hkall] at Hkusers
  have hsk : sk = delRole st0 role := by
    have hu := auth.usersAfter_all st1.users sk.users names role Hmem Hkusers
    cases sk
    simp only at Hken Hkrev Hkroles hu
    rw [hst1] at Hken Hkrev Hkroles hu
    simp only [delRole, Hken, Hkrev, Hkroles, hu]
  subst hsk
  (try wp_auto)
  ihave %Hpk := authOwnF_last_permKeysOk M hs $$ Hown
  have hstep : roleDeleteF en role st0 = .next (bump (delRole st0 role)) := by
    simp [roleDeleteF, hnr, Hrr.1]
  obtain ⟨Hrevfit, Hfit⟩ := Hok en st0 Hl0
  have Hfit' := Hfit _ _ rfl hstep
  wp_apply (h_commitRevision st R M P f T ti Lk (delRole st0 role) Post hs st0)
    $$ [$Hinv $HLk $HL $Hown] as ⟨%rev, %Hrev, HL, Hown⟩
  · ipureintro
    refine ⟨Hl0, rfl, Hrevfit, fun h1 h2 => permKeysOk_delRole _ _ (Hpk st0 Hl0 h1 h2), ?_⟩
    intro hM; subst hM; exact Hl0
  have Hl1 := histLast_after M hs (delRole st0 role) rev (fun h => by subst h; exact Hl0) Hrev
  imod (authSnapF_of_last M _ _ Hl1) $$ Hown with ⟨Hown, #Hsnap⟩
  (try wp_auto)
  wp_bind (App (Val (st @!! go.GoType.PointerType authStore.ty @!! go!"refreshRangePermCache"))
    (Val #(GoInterface.ok ti)))
  iapply (h_refresh st R M ti (fun x => Lk x Post)
      ({ delRole st0 role with revision := rev } : AuthState) (hs ++ [bump (delRole st0 role)]))
    $$ [HL Hca Hown]
  · iframe Hpkg Hinv
    isplitl [Hca]
    · iapply (cacheHalf_of_at _ _ _) $$ Hca Hcsn
    isplitr
    · iapply HRd
    isplitl [HL]
    · iExactEq HL
      all_goals (first | rfl | simp [delRole])
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
  wp_alloc resp as Hresp
  icases typedPointsto_split _ _ _ $$ Hresp with Hresp
  simp only [TypedPointsto.typedPointstoDef]
  iNamed Hresp
  (try wp_auto)
  wp_apply HUnlock $$ %_ %Post %(hs ++ [bump (delRole st0 role)]) [HL $Hown]
    as ⟨HPost, HT, Hown⟩
  · isplitl [HL]
    · iExactEq HL
      all_goals (first | rfl | simp [delRole])
    ipureintro; exact Hl1
  (try wp_auto)
  iapply HΦ
  iexists en, ({ delRole st0 role with revision := rev } : AuthState)
  isplitl [HPost]
  · ileft; iexact HPost
  isplitl [Hbe HT Hen HenQ Hca]
  · iunfold authWRx; iunfold flagAt; iframe HT Hen HenQ Hev Hca Hsnap; iexists (GoInterface.ok bi); iframe Hbe Hbeok
  isplitl [Header]
  · iunfold respOk; isplitr
    · ipureintro; intro h; exact absurd rfl h
    · iright; iexists _; iexact Header
  iexists en
  iframe Hev
  iunfold adminOutP
  iright
  iexists st0, (.next (bump (delRole st0 role)))
  isplitr
  · ipureintro; exact tieStep_refresh M hs _ _ sc0 _ st0 Hl0 Hl1 rfl
  isplitr
  · ipureintro; exact ⟨Hl0, hstep.symm⟩
  simp only [outRes]
  isplitl [Hown]
  · iExactEq Hown
    all_goals (first | rfl | simp [delRole])
  · ipureintro; trivial


theorem auth.authStore.RoleDelete.wp_proof
    (h_commitRevision : auth.authStore.commitRevision.spec (GF := GF) (hG := hG))
    (h_refresh : auth.authStore.refreshRangePermCache.spec (GF := GF) (hG := hG))
    (h_String : zap.String.spec (GF := GF) (hG := hG))
    (h_Error : zap.Logger.Error.spec (GF := GF) (hG := hG))
    (h_Info : zap.Logger.Info.spec (GF := GF) (hG := hG)) :
    auth.authStore.RoleDelete.spec (GF := GF) (hG := hG) :=
  auth.authStore.RoleDelete.spec_of_T (auth.authStore.RoleDelete.wp_tie h_commitRevision h_refresh h_String h_Error h_Info)

end proof

end EtcdGrove
end Perennial
