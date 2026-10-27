/-
Proof of the spec of the same name (the auth plan's S4d, 2026-10-24). Lean-first (no Rocq
counterpart). The role's message is the caller's (`roleOutX`, the write side's read): the search
for the first permission whose key is not below the new one's (`sort.Search`, at any index:
`auth.wp_Search_any`, nothing records that the permissions are sorted) finds an entry of the
same key and range end, whose type is overwritten in place, or the new permission is appended and
the permissions sorted by key (`sort.Sort(permSlice(...))`, `auth.permSlice_isSorter`); either way
the model's step (`roleGrantPermissionR`, `GrantPermLemmas.lean`).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.auth.authStore__RoleGrantPermission
public import Proof.go_etcd_io.etcd.server.v3.auth.LatestTie
public import Spec.go_etcd_io.etcd.server.v3.auth.authStore__refreshRangePermCache
public import Spec.go_etcd_io.etcd.server.v3.auth.authStore__commitRevision
public import Spec.go_etcd_io.etcd.server.v3.auth.isValidPermissionRange
public import Spec.go_uber_org.zap.String
public import Spec.go_uber_org.zap.ByteString
public import Spec.go_uber_org.zap.Logger__Info
public import Proof.go_etcd_io.etcd.server.v3.auth.AdminLemmas
public import Proof.go_etcd_io.etcd.server.v3.auth.PermSorter
public import Proof.go_etcd_io.etcd.server.v3.auth.SearchAny
public import Perennial.Proof.sort.Link
public import Perennial.Proof.bytes.Link

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

theorem auth.roleOutX_null (st : AuthState) (name : GoString) :
    roleOutX (GF := GF) null st name ⊢ ⌜st.roles !! name = none⌝ := by
  unfold roleOutX
  cases h : st.roles !! name with
  | none => iintro -; ipureintro; rfl
  | some ps =>
    iintro ⟨%rr, -, Hr⟩
    iunfold ownRoleX at Hr
    icases Hr with ⟨%s1, %n, %kp, %pl, %uf, %sc, Hp, -⟩
    ihave %Hnn := typedPointsto_not_null $$ Hp
    exact absurd rfl Hnn

theorem auth.roleOutX_some (r : Loc) (st : AuthState) (name : GoString) (hnn : r ≠ null) :
    roleOutX (GF := GF) r st name ⊢ ∃ (ps : Role) (rr : RoleRec),
      ⌜st.roles !! name = some ps ∧ rr.name = name ∧ rr.toRole = ps⌝ ∗ ownRoleX r rr := by
  unfold roleOutX
  cases h : st.roles !! name with
  | none => iintro %Hn; exact absurd Hn hnn
  | some ps =>
    iintro ⟨%rr, %Hrr, Hr⟩
    iexists ps, rr
    iframe Hr
    ipureintro; exact ⟨rfl, Hrr.1, Hrr.2⟩

/-- The `Key` of an owned permission message. -/
theorem auth.wp_permX_key (p : Loc) (w : PermW) :
    {{ ownPermX (GF := GF) p w }}
      (App (Val (GoInstruction (GoLoad (go.GoType.SliceType go.byte))))
        (Val #(structFieldRef authpb.Permission go!"Key" p)))
    {{ (k : GoSlice), RET #k; ownPermX p w ∗ k ↦*□ w.key }} := by
  wp_start as Hp
  iunfold ownPermX at Hp
  icases Hp with ⟨%Hpn, %st, %k, %re, %uf, %sc, Hm, #Hk, #Hre⟩
  icases typedPointsto_split _ _ _ $$ Hm with Hm
  simp only [TypedPointsto.typedPointstoDef]
  iNamed Hm
  wp_apply (IntoValTyped.wp_load (t := go.GoType.SliceType go.byte) _ _ _) $$ Key as Key
  iapply HΦ
  iframe Hk
  iunfold ownPermX
  isplitr
  · ipureintro; exact Hpn
  iexists st, k, re, uf, sc
  iframe Hk Hre
  iapply typedPointsto_combine p _ _ Hpn.1
  simp only [TypedPointsto.typedPointstoDef]
  iframe

/-- The `RangeEnd` of an owned permission message. -/
theorem auth.wp_permX_rangeEnd (p : Loc) (w : PermW) :
    {{ ownPermX (GF := GF) p w }}
      (App (Val (GoInstruction (GoLoad (go.GoType.SliceType go.byte))))
        (Val #(structFieldRef authpb.Permission go!"RangeEnd" p)))
    {{ (k : GoSlice), RET #k; ownPermX p w ∗ k ↦*□ w.rangeEnd }} := by
  wp_start as Hp
  iunfold ownPermX at Hp
  icases Hp with ⟨%Hpn, %st, %k, %re, %uf, %sc, Hm, #Hk, #Hre⟩
  icases typedPointsto_split _ _ _ $$ Hm with Hm
  simp only [TypedPointsto.typedPointstoDef]
  iNamed Hm
  wp_apply (IntoValTyped.wp_load (t := go.GoType.SliceType go.byte) _ _ _) $$ RangeEnd as RangeEnd
  iapply HΦ
  iframe Hre
  iunfold ownPermX
  isplitr
  · ipureintro; exact Hpn
  iexists st, k, re, uf, sc
  iframe Hk Hre
  iapply typedPointsto_combine p _ _ Hpn.1
  simp only [TypedPointsto.typedPointstoDef]
  iframe

/-- The `PermType` of an owned permission message set. -/
theorem auth.wp_permX_setTy (p : Loc) (w : PermW) (ty : w32) :
    {{ ownPermX (GF := GF) p w }}
      (App (Val (GoInstruction (GoStore go_etcd_io.etcd.api.v3.authpb.Permission_Type.ty)))
        (Val (PairV #(structFieldRef authpb.Permission go!"PermType" p) #ty)))
    {{ RET #(); ownPermX p { w with ty := ty } }} := by
  wp_start as Hp
  iunfold ownPermX at Hp
  icases Hp with ⟨%Hpn, %st, %k, %re, %uf, %sc, Hm, #Hk, #Hre⟩
  icases typedPointsto_split _ _ _ $$ Hm with Hm
  simp only [TypedPointsto.typedPointstoDef]
  iNamed Hm
  wp_apply (IntoValTyped.wp_store (t := go_etcd_io.etcd.api.v3.authpb.Permission_Type.ty) _ _ _)
    $$ PermType as PermType
  iapply HΦ
  iunfold ownPermX
  isplitr
  · ipureintro; exact Hpn
  iexists st, k, re, uf, sc
  iframe Hk Hre
  iapply typedPointsto_combine p _ _ Hpn.1
  simp only [TypedPointsto.typedPointstoDef]
  iframe

theorem auth.authStore.RoleGrantPermission.wp_tieB
    (h_commitRevision : auth.authStore.commitRevision.spec (GF := GF) (hG := hG))
    (h_refresh : auth.authStore.refreshRangePermCache.spec (GF := GF) (hG := hG))
    (h_valid : auth.isValidPermissionRange.spec (GF := GF) (hG := hG))
    (h_String : zap.String.spec (GF := GF) (hG := hG))
    (h_ByteString : zap.ByteString.spec (GF := GF) (hG := hG))
    (h_Info : zap.Logger.Info.spec (GF := GF) (hG := hG)) :
    auth.authStore.RoleGrantPermission.specTB (GF := GF) (hG := hG) := by
  intro st R M P f T hs Pre Q Post r name w b0 sc0 be
  wp_start as ⟨#Hinv, #Hr, %Hnamelen, Hown, HWR, Hcs, %Hok⟩
  ihave #Htn : auth.typeNamesOk (GF := GF) $$ []
  · iapply auth.typeNamesOk_of_init
    iPkgInit
  icases authErrVar_of_init .permissionNotGiven $$ Hpkg with ⟨%ePNG, #HePNG⟩
  icases authErrVar_of_init .invalidAuthMgmt $$ Hpkg with ⟨%eIAM, #HeIAM⟩
  icases authErrVar_of_init .roleNotFound $$ Hpkg with ⟨%eRNF, #HeRNF⟩
  simp only [AuthErr.var]
  ihave #Hsortpkg : isPkgInit (PROP := IProp GF) pkg_id.sort $$ []
  · iPkgInit
  ihave #Hbpkg : isPkgInit (PROP := IProp GF) pkg_id.bytes $$ []
  · iPkgInit
  ihave #Hinv' := Hinv
  iunfold authInv at Hinv'
  icases Hinv' with ⟨%Hst, -, ⟨%lg, #Hlg, %Hlgnn⟩, -, -, -, -⟩
  iunfold roleGrantPermissionReqIs at Hr
  icases Hr with ⟨%Hrnn, #HN, %pp, #HP, Hw⟩
  (try wp_auto)
  iunfold authWRxB at HWR
  icases HWR with ⟨⟨Hbe, #Hbeok⟩, HT, Hfl, #Hev, Hca, #Hcsn⟩
  ihave #Hbeok' := Hbeok
  iunfold authWBackendOk at Hbeok'
  icases Hbeok' with ⟨%bi, %Hbi, #HBatch, #HFC, -⟩
  subst Hbi
  wp_apply wp_with_defer as %defer defer
  (try wp_auto)
  cases w with
  | none =>
    ihave %Hpn : ⌜pp = null⌝ $$ [Hw]
    · iexact Hw
    subst Hpn
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
    iexists st0, (.err .permissionNotGiven)
    isplitr
    · ipureintro; exact tieStep_same _ _ _ _
    isplitr
    · ipureintro; exact ⟨Hl, rfl⟩
    simp only [outRes, authErrOf, AuthErr.var]
    iframe Hown
    iexists ePNG; iframe HePNG; ipureintro; rfl
  | some w =>
    ihave #Hw' := Hw
    iunfold ownPermW at Hw'
    icases Hw' with ⟨%Hwp, %wst, %wk, %wre, %wuf, %wsc, #Hwm, #Hwk, #Hwre⟩
    have hpp : pp ≠ null := Hwp.1
    simp only [hpp, decide_false]
    (try wp_auto)
    icases typedPointsto_split _ _ _ $$ Hwm with #Hwm'
    simp only [TypedPointsto.typedPointstoDef]
    iNamed Hwm'
    (try wp_auto)
    wp_apply (h_valid wk wre w.key w.rangeEnd DFrac.discard DFrac.discard) $$ [$Hwk $Hwre]
      as %bv ⟨-, -, %Hbv⟩
    (try wp_auto)
    cases bv
    · -- an invalid range
      simp only [Bool.not_false]
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
      iexists st0, (.err .invalidAuthMgmt)
      isplitr
      · ipureintro; exact tieStep_same _ _ _ _
      isplitr
      · ipureintro
        refine ⟨Hl, ?_⟩
        have hnv : ¬ rangeValid w.key w.rangeEnd := fun h => by
          have := Hbv.mpr h; cases this
        simp [roleGrantPermissionR, hnv]
      simp only [outRes, authErrOf, AuthErr.var]
      iframe Hown
      iexists eIAM; iframe HeIAM; ipureintro; rfl
    have hvalid : rangeValid w.key w.rangeEnd := Hbv.mp rfl
    simp only [Bool.not_true]
    (try wp_auto)
    wp_apply HBatch as %tx Htx
    iunfold authBatchTxOk at Htx
    icases Htx with ⟨%ti, %Hti, %Lk, #HLk⟩
    subst Hti
    ihave #HLk' := HLk
    iunfold authBatchTxLk at HLk'
    icases HLk' with ⟨#HLock, #HRd, -, -, #HPutR, -, -, -, #HUnlock, -, #HRGX⟩
    (try wp_auto)
    wp_bind (App (Val #(methods ti.ty go!"Lock" ti.v)) (Val #()))
    iapply HLock $$ %hs %Pre %Q %Post [$Hcs $HT $Hown]
    inext
    iintro ⟨%st0, HL, Hown, %Hl0⟩
    (try wp_auto)
    wp_bind (App (Val #(methods ti.ty go!"UnsafeGetRole" ti.v)) (Val #name))
    iapply HRGX $$ %st0 %Post %name HL
    inext
    iintro %rl ⟨HL, Hrl⟩
    (try wp_auto)
    wp_if_destruct
    · ihave %Hrnone := auth.roleOutX_null st0 name $$ Hrl
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
        simp [roleGrantPermissionR, hvalid, Hrnone]
      simp only [outRes, authErrOf, AuthErr.var]
      iframe Hown
      iexists eRNF; iframe HeRNF; ipureintro; rfl
    ihave Hrl' := auth.roleOutX_some rl st0 name Hif $$ Hrl
    icases Hrl' with ⟨%ps, %rr, %Hrr, Hrm⟩
    obtain ⟨Hlook, Hrrn, Hrrp⟩ := Hrr
    iunfold ownRoleX at Hrm
    icases Hrm with ⟨%rst, %rnm, %kp, %locs, %ruf, %rsc, Hrp, #Hrnm, Hkp, Hkpc, %Hlocs, Hperms⟩
    icases typedPointsto_split _ _ _ $$ Hrp with Hrp
    simp only [TypedPointsto.typedPointstoDef]
    iNamed Hrp
    (try wp_auto)
    ihave %Hkpl := ownSlice_len _ _ _ $$ Hkp
    have hzl : (locs.zip rr.perms).length = locs.length := by
      rw [List.length_zip, Hlocs.1, Nat.min_self]
    let fs : Int → Bool := fun i => match rr.perms[i.toNat]? with
      | some q => decide (¬ go.GoStringLt q.key w.key)
      | none => false
    wp_apply (auth.wp_Search_any kp.len _ fs
        iprop(role_ptr ↦ rl ∗ structFieldRef authpb.Role go!"KeyPermission" rl ↦ kp ∗ kp ↦* locs ∗
          r_ptr ↦ r ∗ [∗list] x ∈ locs.zip rr.perms, ownPermX x.1 x.2))
      $$ [role KeyPermission Hkp r Hperms] as %idx ⟨⟨role, KeyPermission, Hkp, r, Hperms⟩, %Hidx⟩
    · iframe role KeyPermission Hkp r Hperms
      isplitr
      · ipureintro; exact Hkpl.2
      iunfold _root_.Perennial.sort.predImplements
      iintro %i %Φc !> ⟨⟨role, KeyPermission, Hkp, r, Hperms⟩, %Hi⟩ HΦc
      wp_auto
      have hlt : (sint.Z i).toNat < locs.length := by
        have := Hkpl.1; word
      obtain ⟨lc, hlc⟩ : ∃ x, locs[(sint.Z i).toNat]? = some x :=
        ⟨_, List.getElem?_eq_getElem hlt⟩
      obtain ⟨q, hq⟩ : ∃ x, rr.perms[(sint.Z i).toNat]? = some x :=
        ⟨_, List.getElem?_eq_getElem (by rw [← Hlocs.1]; exact hlt)⟩
      have hz : (locs.zip rr.perms)[(sint.Z i).toNat]? = some (lc, q) := by
        simp [List.getElem?_zip_eq_some, hlc, hq]
      simp only [Hi, _root_.and_self, ↓reduceIte]
      wp_apply wp_load_slice_index kp (sint.Z i) locs (DFrac.own 1) lc Hi.1 $$ [$Hkp] as Hkp
      · ipureintro; exact hlc
      ihave ⟨Hx, Hc⟩ := (BigSepL.bigSepL_lookup_acc
        (Φ := fun _ x => iprop(ownPermX (GF := GF) x.1 x.2)) hz).1 $$ Hperms
      wp_apply auth.wp_permX_key lc q $$ [$Hx] as %k ⟨Hx, #Hk⟩
      have hset : (locs.zip rr.perms).set (sint.Z i).toNat (lc, q) = locs.zip rr.perms := by
        obtain ⟨hlt', hget⟩ := List.getElem?_eq_some_iff.mp hz
        rw [← hget]; exact List.set_getElem_self hlt'
      ihave Hperms := Hc $$ %(lc, q) Hx
      rw [hset]
      (try wp_auto)
      wp_apply (_root_.Perennial.bytes.wp_Compare k wk DFrac.discard DFrac.discard q.key w.key)
        $$ [$Hk $Hwk] as ⟨-, -⟩
      (try wp_auto)
      iapply HΦc
      iframe role KeyPermission Hkp r Hperms
      ipureintro
      simp only [fs, hq]
      unfold bytes.compareResult
      by_cases h1 : go.GoStringLt q.key w.key
      · rw [if_pos h1]; simp only [h1, not_true_eq_false, decide_false]; decide
      · rw [if_neg h1]; simp only [h1, not_false_eq_true, decide_true]
        by_cases h2 : q.key = w.key
        · rw [if_pos h2]; decide
        · rw [if_neg h2]; decide
    (try wp_auto)
    have hzl' : locs.length = rr.perms.length := Hlocs.1
    let fb : Bool := match rr.perms[(sint.Z idx).toNat]? with
      | some q => decide (q.key = w.key) && decide (q.rangeEnd = w.rangeEnd)
      | none => false
    wp_join (Q := fun v => iprop(⌜v = #fb⌝ ∗ role_ptr ↦ rl ∗
        structFieldRef authpb.Role go!"KeyPermission" rl ↦ kp ∗ kp ↦* locs ∗ r_ptr ↦ r ∗
        idx_ptr ↦ idx ∗ [∗list] x ∈ locs.zip rr.perms, ownPermX x.1 x.2))
      at (if: _ then _ else #false) with [role KeyPermission Hkp r idx Hperms]
      as ⟨%Hv, role, KeyPermission, Hkp, r, idx, Hperms⟩
    · wp_if_destruct
      · -- the index is in range
        have hlt : (sint.Z idx).toNat < locs.length := by have := Hkpl.1; word
        obtain ⟨lc, hlc⟩ : ∃ x, locs[(sint.Z idx).toNat]? = some x :=
          ⟨_, List.getElem?_eq_getElem hlt⟩
        obtain ⟨q, hq⟩ : ∃ x, rr.perms[(sint.Z idx).toNat]? = some x :=
          ⟨_, List.getElem?_eq_getElem (by rw [← hzl']; exact hlt)⟩
        have hz : (locs.zip rr.perms)[(sint.Z idx).toNat]? = some (lc, q) := by
          simp [List.getElem?_zip_eq_some, hlc, hq]
        have hset : (locs.zip rr.perms).set (sint.Z idx).toNat (lc, q) = locs.zip rr.perms := by
          obtain ⟨hlt', hget⟩ := List.getElem?_eq_some_iff.mp hz
          rw [← hget]; exact List.set_getElem_self hlt'
        have hb : 0 ≤ sint.Z idx ∧ sint.Z idx < sint.Z kp.len := ⟨Hidx.1, Hif⟩
        (try wp_auto)
        simp only [hb, _root_.and_self, ↓reduceIte]
        wp_apply wp_load_slice_index kp (sint.Z idx) locs (DFrac.own 1) lc Hidx.1 $$ [$Hkp] as Hkp
        · ipureintro; exact hlc
        ihave ⟨Hx, Hc⟩ := (BigSepL.bigSepL_lookup_acc
          (Φ := fun _ x => iprop(ownPermX (GF := GF) x.1 x.2)) hz).1 $$ Hperms
        wp_apply auth.wp_permX_key lc q $$ [$Hx] as %k ⟨Hx, #Hk⟩
        (try wp_auto)
        wp_apply (_root_.Perennial.bytes.wp_Equal k wk DFrac.discard DFrac.discard q.key w.key)
          $$ [$Hk $Hwk] as ⟨-, -⟩
        wp_if_destruct
        · -- the same key: compare the range ends
          (try wp_auto)
          simp only [hb, _root_.and_self, ↓reduceIte]
          wp_apply wp_load_slice_index kp (sint.Z idx) locs (DFrac.own 1) lc Hidx.1 $$ [$Hkp] as Hkp
          · ipureintro; exact hlc
          wp_apply auth.wp_permX_rangeEnd lc q $$ [$Hx] as %re ⟨Hx, #Hre⟩
          (try wp_auto)
          wp_apply (_root_.Perennial.bytes.wp_Equal re wre DFrac.discard DFrac.discard q.rangeEnd
            w.rangeEnd) $$ [$Hre $Hwre] as ⟨-, -⟩
          ihave Hperms := Hc $$ %(lc, q) Hx
          rw [hset]
          iframe
          ipureintro
          simp only [fb, hq, Hif, decide_true, Bool.true_and]
        · (try wp_auto)
          ihave Hperms := Hc $$ %(lc, q) Hx
          rw [hset]
          iframe
          ipureintro
          simp only [fb, hq, Hif, decide_false, Bool.false_and]
      · (try wp_auto)
        iframe
        ipureintro
        have hnone : rr.perms[(sint.Z idx).toNat]? = none := by
          apply List.getElem?_eq_none
          have := Hkpl.1; rw [← hzl']; word
        simp only [fb, hnone]
    subst Hv
    cases hfb : fb
    rotate_left
    · -- the entry of the same key and range end: its type set in place
      obtain ⟨q, hq, hqk, hqre⟩ : ∃ q, rr.perms[(sint.Z idx).toNat]? = some q ∧ q.key = w.key ∧
          q.rangeEnd = w.rangeEnd := by
        cases h : rr.perms[(sint.Z idx).toNat]? with
        | none => simp [fb, h] at hfb
        | some q =>
          simp only [fb, h, Bool.and_eq_true, decide_eq_true_eq] at hfb
          exact ⟨q, rfl, hfb.1, hfb.2⟩
      have hlt : (sint.Z idx).toNat < locs.length := by
        rw [hzl']; exact (List.getElem?_eq_some_iff.mp hq).1
      obtain ⟨lc, hlc⟩ : ∃ x, locs[(sint.Z idx).toNat]? = some x :=
        ⟨_, List.getElem?_eq_getElem hlt⟩
      have hz : (locs.zip rr.perms)[(sint.Z idx).toNat]? = some (lc, q) := by
        simp [List.getElem?_zip_eq_some, hlc, hq]
      have hb : 0 ≤ sint.Z idx ∧ sint.Z idx < sint.Z kp.len := by
        refine ⟨Hidx.1, ?_⟩; have := Hkpl.1; word
      (try wp_auto)
      (try simp only [hb, _root_.and_self, ↓reduceIte])
      (try wp_auto)
      (try simp only [hb, _root_.and_self, ↓reduceIte])
      wp_apply wp_load_slice_index kp (sint.Z idx) locs (DFrac.own 1) lc Hidx.1 $$ [$Hkp] as Hkp
      · ipureintro; exact hlc
      ihave ⟨Hx, Hc⟩ := (BigSepL.bigSepL_lookup_acc
        (Φ := fun _ x => iprop(ownPermX (GF := GF) x.1 x.2)) hz).1 $$ Hperms
      (try wp_auto)
      wp_apply auth.wp_permX_setTy lc q w.ty $$ [$Hx] as Hx
      have hqw : ({ q with ty := w.ty } : PermW) = w := by
        cases q; cases w; simp_all
      rw [hqw]
      ihave Hperms := Hc $$ %(lc, w) Hx
      rw [auth.zip_set_left locs rr.perms _ lc w hlc]
      (try wp_auto)
      ihave Hrm : ownRoleX rl ({ rr with perms := rr.perms.set (sint.Z idx).toNat w } : RoleRec)
        $$ [state Name KeyPermission unknownFields sizeCache Hkp Hkpc Hperms]
      · iunfold ownRoleX
        iexists rst, rnm, kp, locs, ruf, rsc
        iframe Hrnm Hkp Hkpc Hperms
        isplitl [state Name KeyPermission unknownFields sizeCache]
        · iapply typedPointsto_combine rl _ _ Hif
          simp only [TypedPointsto.typedPointstoDef]
          iframe
        ipureintro; simp only [List.length_set]; exact Hlocs
      imod auth.ownRoleX_persist rl _ $$ Hrm with Hrm
      ihave %Hpk := authOwnF_last_permKeysOk M hs $$ Hown
      have hstep := auth.grant_update name st0 rr ps _ q w Hlook Hrrp hq hqk hqre hvalid
      have hkeys : M.isOn = true → M ≠ .any →
          ∀ p ∈ ({ rr with perms := rr.perms.set (sint.Z idx).toNat w } : RoleRec).toRole,
            p.key ≠ [] := fun h1 h2 =>
        auth.grant_keys_update rr _ w hvalid.1 (fun p hp => Hpk st0 Hl0 h1 h2 name ps Hlook p
          (Hrrp ▸ hp))
      have hrn : ({ rr with perms := rr.perms.set (sint.Z idx).toNat w } : RoleRec).name = name := Hrrn
      generalize ({ rr with perms := rr.perms.set (sint.Z idx).toNat w } : RoleRec) = rr' at hstep hkeys hrn ⊢
      wp_bind (App (Val #(methods ti.ty go!"UnsafePutRole" ti.v)) (Val #rl))
      iapply HPutR $$ %st0 %Post %rl %rr' [HL Hrm]
      · iframe HL Hrm; ipureintro; rw [hrn]; exact Hnamelen
      inext
      iintro ⟨HL, Hrr⟩
      (try wp_auto)
      ihave HL : Lk (putRole st0 name rr'.toRole) Post $$ [HL]
      · iExactEq HL; rw [hrn]
      obtain ⟨Hrevfit, Hfit⟩ := Hok st0 Hl0
      have Hfit' := Hfit _ _ hstep rfl
      wp_apply (h_commitRevision st R M P f T ti Lk (putRole st0 name rr'.toRole) Post hs st0)
        $$ [$Hinv $HLk $HL $Hown] as ⟨%rev, %Hrev, HL, Hown⟩
      · ipureintro
        refine ⟨Hl0, rfl, Hrevfit, fun h1 h2 =>
          permKeysOk_putRole _ _ _ (Hpk st0 Hl0 h1 h2) (hkeys h1 h2), ?_⟩
        intro hM; subst hM; exact Hl0
      have Hl1 := histLast_after M hs (putRole st0 name rr'.toRole) rev
        (fun h => by subst h; exact Hl0) Hrev
      imod (authSnapF_of_last M _ _ Hl1) $$ Hown with ⟨Hown, #Hsnap⟩
      (try wp_auto)
      wp_bind (App (Val (st @!! go.GoType.PointerType authStore.ty @!! go!"refreshRangePermCache"))
        (Val #(GoInterface.ok ti)))
      iapply (h_refresh st R M ti (fun x => Lk x Post)
          ({ putRole st0 name rr'.toRole with revision := rev } : AuthState) (hs ++ [bump (putRole st0 name rr'.toRole)]))
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
      ihave #Htn' := Htn
      iunfold auth.typeNamesOk at Htn'
      icases Htn' with ⟨%mp, %Mn, #Hgm, #Hmn⟩
      wp_apply h_String _ _ as %f1 -
      (try wp_auto)
      wp_apply (wp_map_lookup1 go.int32 go.string mp Mn w.ty DFrac.discard) $$ [$Hmn] as -
      (try wp_auto)
      wp_apply h_String _ _ as %f2 -
      (try wp_auto)
      wp_apply h_ByteString _ _ as %f3 -
      (try wp_auto)
      wp_apply h_ByteString _ _ as %f4 -
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
      wp_apply HUnlock $$ %_ %Post %(hs ++ [bump (putRole st0 name rr'.toRole)]) [HL $Hown]
        as ⟨HPost, HT, Hown⟩
      · isplitl [HL]
        · iExactEq HL
          all_goals rfl
        ipureintro; exact Hl1
      (try wp_auto)
      iapply HΦ
      iexists b0, ({ putRole st0 name rr'.toRole with revision := rev } : AuthState)
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
      iexists st0, (.next (bump (putRole st0 name rr'.toRole)))
      isplitr
      · ipureintro; exact tieStep_refresh M hs _ b0 sc0 _ st0 Hl0 Hl1 rfl
      isplitr
      · ipureintro; exact ⟨Hl0, hstep⟩
      simp only [outRes]
      isplitl [Hown]
      · iExactEq Hown
        all_goals rfl
      · ipureintro; trivial
    · -- no such entry: the permission appended, the permissions sorted by key
      (try wp_auto)
      ihave %Hnpn := typedPointsto_not_null $$ «$r0»
      ipersist «$r0»
      ihave #Hnpw : ownPermW «$r0_ptr» w $$ []
      · iunfold ownPermW
        isplitr
        · ipureintro; exact ⟨Hnpn, Hwp.2⟩
        iexists _, wk, wre, _, _
        iframe Hwk Hwre
        iexact «$r0»
      ihave Hperms' : |==> [∗list] x ∈ locs.zip rr.perms, ownPermW x.1 x.2 $$ [Hperms]
      · iapply BigSepL.bigSepL_bupd
        iapply (BigSepL.bigSepL_mono (fun {_ x} _ => ownPermX_persist x.1 x.2)) $$ Hperms
      imod Hperms' with #Hperms'
      ihave #Hpw : □ (∀ x : Loc × PermW, ⌜x ∈ locs.zip rr.perms⌝ → ownPermW x.1 x.2) $$ []
      · iintro !> %x %Hx
        obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp Hx
        iapply (BigSepL.bigSepL_lookup (Φ := fun _ x => iprop(ownPermW (GF := GF) x.1 x.2)) hi)
        iexact Hperms'
      wp_apply wp_slice_literal (V := Loc) [«$r0_ptr»]
      isplitr
      · ipureintro; rfl
      iintro %sl1 ⟨Hsl1, -⟩
      (try wp_auto)
      wp_apply (wp_slice_append kp locs _ [«$r0_ptr»] (DFrac.own 1)) $$ [$Hkp $Hkpc $Hsl1]
        as %s2 ⟨Hs2, Hs2c, -⟩
      (try wp_auto)
      ihave #Hsrt := auth.permSlice_isSorter s2 $$ Hpkg
      have hfst : (locs.zip rr.perms ++ [(«$r0_ptr», w)]).map Prod.fst = locs ++ [«$r0_ptr»] := by
        rw [List.map_append, List.map_fst_zip (by omega)]; rfl
      wp_apply (_root_.Perennial.sort.wp_Sort (interface.mk permSlice.ty #s2) (auth.permsOwn s2) keyLt
          StrictWeakOrder_keyLt (locs.zip rr.perms ++ [(«$r0_ptr», w)])) $$ [Hs2]
        as %xs' ⟨Hxs, %Hperm, %Hsorted⟩
      · iframe Hsrt
        isplitl [Hs2]
        · iunfold auth.permsOwn
          isplitl [Hs2]
          · iExactEq Hs2; rw [hfst]
          iintro !> %x %Hx
          rcases List.mem_append.mp Hx with h | h
          · iapply Hpw; ipureintro; exact h
          · simp only [List.mem_singleton] at h; subst h; iexact Hnpw
        ipureintro
        rw [List.length_append, List.length_zip, Hlocs.1, Nat.min_self]
        have := Hlocs.2; simp only [List.length_singleton]; omega
      (try wp_auto)
      iunfold auth.permsOwn at Hxs
      icases Hxs with ⟨Hxs, #Hxw⟩
      imod (ownSlice_persist _ _ _) $$ Hxs with #Hxs
      have hzz : (xs'.map Prod.fst).zip (xs'.map Prod.snd) = xs' := by
        rw [← List.unzip_fst, ← List.unzip_snd, List.zip_unzip]
      ihave Hrm : ownRole rl ({ rr with perms := xs'.map Prod.snd } : RoleRec)
        $$ [state Name KeyPermission unknownFields sizeCache]
      · iunfold ownRole
        iexists rst, rnm, s2, xs'.map Prod.fst, ruf, rsc
        iframe Hrnm Hxs
        isplitl [state Name KeyPermission unknownFields sizeCache]
        · iapply typedPointsto_combine rl _ _ Hif
          simp only [TypedPointsto.typedPointstoDef]
          iframe
        isplitr
        · ipureintro; simp
        simp only
        rw [hzz]
        have hintro := BigSepL.bigSepL_intro (PROP := IProp GF) (l := xs')
          (P := iprop(□ (∀ x : Loc × PermW, ⌜x ∈ xs'⌝ → ownPermW (GF := GF) x.1 x.2)))
          (Φ := fun (_ : Nat) (x : Loc × PermW) => iprop(ownPermW (GF := GF) x.1 x.2))
          (fun k x hk => by
            iintro #H
            iapply H; ipureintro; exact List.mem_of_getElem? hk)
        iapply hintro
        iexact Hxw
      ihave %Hpk := authOwnF_last_permKeysOk M hs $$ Hown
      have hstep := auth.grant_insert name st0 rr ps w locs «$r0_ptr» xs' Hlook Hrrp hzl' Hperm hvalid
      have hkeys : M.isOn = true → M ≠ .any →
          ∀ p ∈ ({ rr with perms := xs'.map Prod.snd } : RoleRec).toRole, p.key ≠ [] := fun h1 h2 =>
        auth.grant_keys_insert rr w locs «$r0_ptr» xs' hzl' Hperm hvalid.1
          (fun p hp => Hpk st0 Hl0 h1 h2 name ps Hlook p (Hrrp ▸ hp))
      have hrn : ({ rr with perms := xs'.map Prod.snd } : RoleRec).name = name := Hrrn
      generalize ({ rr with perms := xs'.map Prod.snd } : RoleRec) = rr' at hstep hkeys hrn ⊢
      wp_bind (App (Val #(methods ti.ty go!"UnsafePutRole" ti.v)) (Val #rl))
      iapply HPutR $$ %st0 %Post %rl %rr' [HL Hrm]
      · iframe HL Hrm; ipureintro; rw [hrn]; exact Hnamelen
      inext
      iintro ⟨HL, Hrr⟩
      (try wp_auto)
      ihave HL : Lk (putRole st0 name rr'.toRole) Post $$ [HL]
      · iExactEq HL; rw [hrn]
      obtain ⟨Hrevfit, Hfit⟩ := Hok st0 Hl0
      have Hfit' := Hfit _ _ hstep rfl
      wp_apply (h_commitRevision st R M P f T ti Lk (putRole st0 name rr'.toRole) Post hs st0)
        $$ [$Hinv $HLk $HL $Hown] as ⟨%rev, %Hrev, HL, Hown⟩
      · ipureintro
        refine ⟨Hl0, rfl, Hrevfit, fun h1 h2 =>
          permKeysOk_putRole _ _ _ (Hpk st0 Hl0 h1 h2) (hkeys h1 h2), ?_⟩
        intro hM; subst hM; exact Hl0
      have Hl1 := histLast_after M hs (putRole st0 name rr'.toRole) rev
        (fun h => by subst h; exact Hl0) Hrev
      imod (authSnapF_of_last M _ _ Hl1) $$ Hown with ⟨Hown, #Hsnap⟩
      (try wp_auto)
      wp_bind (App (Val (st @!! go.GoType.PointerType authStore.ty @!! go!"refreshRangePermCache"))
        (Val #(GoInterface.ok ti)))
      iapply (h_refresh st R M ti (fun x => Lk x Post)
          ({ putRole st0 name rr'.toRole with revision := rev } : AuthState) (hs ++ [bump (putRole st0 name rr'.toRole)]))
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
      ihave #Htn' := Htn
      iunfold auth.typeNamesOk at Htn'
      icases Htn' with ⟨%mp, %Mn, #Hgm, #Hmn⟩
      wp_apply h_String _ _ as %f1 -
      (try wp_auto)
      wp_apply (wp_map_lookup1 go.int32 go.string mp Mn w.ty DFrac.discard) $$ [$Hmn] as -
      (try wp_auto)
      wp_apply h_String _ _ as %f2 -
      (try wp_auto)
      wp_apply h_ByteString _ _ as %f3 -
      (try wp_auto)
      wp_apply h_ByteString _ _ as %f4 -
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
      wp_apply HUnlock $$ %_ %Post %(hs ++ [bump (putRole st0 name rr'.toRole)]) [HL $Hown]
        as ⟨HPost, HT, Hown⟩
      · isplitl [HL]
        · iExactEq HL
          all_goals rfl
        ipureintro; exact Hl1
      (try wp_auto)
      iapply HΦ
      iexists b0, ({ putRole st0 name rr'.toRole with revision := rev } : AuthState)
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
      iexists st0, (.next (bump (putRole st0 name rr'.toRole)))
      isplitr
      · ipureintro; exact tieStep_refresh M hs _ b0 sc0 _ st0 Hl0 Hl1 rfl
      isplitr
      · ipureintro; exact ⟨Hl0, hstep⟩
      simp only [outRes]
      isplitl [Hown]
      · iExactEq Hown
        all_goals rfl
      · ipureintro; trivial


theorem auth.authStore.RoleGrantPermission.wp_tie
    (h_commitRevision : auth.authStore.commitRevision.spec (GF := GF) (hG := hG))
    (h_refresh : auth.authStore.refreshRangePermCache.spec (GF := GF) (hG := hG))
    (h_valid : auth.isValidPermissionRange.spec (GF := GF) (hG := hG))
    (h_String : zap.String.spec (GF := GF) (hG := hG))
    (h_ByteString : zap.ByteString.spec (GF := GF) (hG := hG))
    (h_Info : zap.Logger.Info.spec (GF := GF) (hG := hG)) :
    auth.authStore.RoleGrantPermission.specT (GF := GF) (hG := hG) :=
  auth.authStore.RoleGrantPermission.specT_of_TB (auth.authStore.RoleGrantPermission.wp_tieB h_commitRevision h_refresh h_valid h_String h_ByteString h_Info)

theorem auth.authStore.RoleGrantPermission.wp_proof
    (h_commitRevision : auth.authStore.commitRevision.spec (GF := GF) (hG := hG))
    (h_refresh : auth.authStore.refreshRangePermCache.spec (GF := GF) (hG := hG))
    (h_valid : auth.isValidPermissionRange.spec (GF := GF) (hG := hG))
    (h_String : zap.String.spec (GF := GF) (hG := hG))
    (h_ByteString : zap.ByteString.spec (GF := GF) (hG := hG))
    (h_Info : zap.Logger.Info.spec (GF := GF) (hG := hG)) :
    auth.authStore.RoleGrantPermission.spec (GF := GF) (hG := hG) :=
  auth.authStore.RoleGrantPermission.spec_of_T (auth.authStore.RoleGrantPermission.wp_tie h_commitRevision h_refresh h_valid h_String h_ByteString h_Info)

end proof

end EtcdGrove
end Perennial
