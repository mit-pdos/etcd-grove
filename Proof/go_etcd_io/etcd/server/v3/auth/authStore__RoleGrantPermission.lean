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
      ⌜st.roles !! name = some ps ∧ rr.name = name ∧ rr.toRole.Perm ps⌝ ∗ ownRoleX r rr := by
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

/-- The `Key` of a read-only permission message. -/
theorem auth.wp_permW_key (p : Loc) (w : PermW) :
    {{ ownPermW (GF := GF) p w }}
      (App (Val (GoInstruction (GoLoad (go.GoType.SliceType go.byte))))
        (Val #(structFieldRef authpb.Permission go!"Key" p)))
    {{ (k : GoSlice), RET #k; k ↦*□ w.key }} := by
  wp_start as #Hp
  iunfold ownPermW at Hp
  icases Hp with ⟨%Hpn, %st, %k, %re, %uf, %sc, #Hm, #Hk, #Hre⟩
  icases typedPointsto_split _ _ _ $$ Hm with #Hm
  simp only [TypedPointsto.typedPointstoDef]
  iNamed Hm
  wp_apply (IntoValTyped.wp_load (t := go.GoType.SliceType go.byte) _ _ _) $$ Key as -
  iapply HΦ
  iexact Hk

/-- The `RangeEnd` of a read-only permission message. -/
theorem auth.wp_permW_rangeEnd (p : Loc) (w : PermW) :
    {{ ownPermW (GF := GF) p w }}
      (App (Val (GoInstruction (GoLoad (go.GoType.SliceType go.byte))))
        (Val #(structFieldRef authpb.Permission go!"RangeEnd" p)))
    {{ (k : GoSlice), RET #k; k ↦*□ w.rangeEnd }} := by
  wp_start as #Hp
  iunfold ownPermW at Hp
  icases Hp with ⟨%Hpn, %st, %k, %re, %uf, %sc, #Hm, #Hk, #Hre⟩
  icases typedPointsto_split _ _ _ $$ Hm with #Hm
  simp only [TypedPointsto.typedPointstoDef]
  iNamed Hm
  wp_apply (IntoValTyped.wp_load (t := go.GoType.SliceType go.byte) _ _ _) $$ RangeEnd as -
  iapply HΦ
  iexact Hre

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
  wp_start as ⟨#Hinv, #Hr, %Hnamelen, Hown, HWR, Hcs, %Hok, #Hcap⟩
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
    ihave %Hkpl := ownSlice_len _ _ _ $$ Hkp
    have hzl' : locs.length = rr.perms.length := Hlocs.1
    -- the permission messages are only read from here on (the fork's code writes none)
    ihave Hperms' : |==> [∗list] x ∈ locs.zip rr.perms, ownPermW x.1 x.2 $$ [Hperms]
    · iapply BigSepL.bigSepL_bupd
      iapply (BigSepL.bigSepL_mono (fun {_ x} _ => ownPermX_persist x.1 x.2)) $$ Hperms
    imod Hperms' with #Hperms'
    ihave #Hpw : □ (∀ x : Loc × PermW, ⌜x ∈ locs.zip rr.perms⌝ → ownPermW x.1 x.2) $$ []
    · iintro !> %x %Hx
      obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp Hx
      iapply (BigSepL.bigSepL_lookup (Φ := fun _ x => iprop(ownPermW (GF := GF) x.1 x.2)) hi)
      iexact Hperms'
    (try wp_auto)
    -- the loop: the pairs kept so far are those of the first `n` off `w`'s range
    let offW : Loc × PermW → Bool := fun x => !permWAt w.key w.rangeEnd x.2
    ihave IH : iprop(∃ (n : w64) (ks : GoSlice) (kl : List (Loc × PermW)) (pv : Loc),
        "i" ∷ i_ptr ↦ n ∗ "kept" ∷ kept_ptr ↦ ks ∗ "perm" ∷ perm_ptr ↦ pv ∗
        "Hkp" ∷ kp ↦* locs ∗
        "Hks" ∷ ks ↦* kl.map Prod.fst ∗ "Hksc" ∷ ownSliceCap Loc ks (DFrac.own 1) ∗
        "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.nat n ≤ locs.length ∧
          kl = ((locs.zip rr.perms).take (sint.nat n)).filter offW⌝) $$ [i kept perm Hkp]
    · iexists W64 0, slice.nil, [], _
      iframe i kept perm Hkp
      simp only [List.map_nil]
      isplitr
      · iapply (ownSlice_nil (V := Loc) (DFrac.own 1))
      isplitr
      · iapply ownSliceCap_nil
      ipureintro
      refine ⟨by word, by word, ?_⟩
      rw [show sint.nat (W64 0) = 0 by rfl]; simp
    irename «as» => Has
    irename : (iprop("_" ∷ True) : IProp GF) => Hjunk
    iclear Hjunk
    wp_for IH
    wp_if_destruct
    · -- an iteration: the permission at `n`
      have Hlt : sint.nat n < locs.length := by have := Hkpl.1; word
      have Hbnd : 0 ≤ sint.Z n ∧ sint.Z n < sint.Z kp.len := ⟨Hn.1, Hif⟩
      simp only [Hbnd, _root_.and_self, ↓reduceIte]
      obtain ⟨lc, hlc⟩ : ∃ x, locs[sint.nat n]? = some x := ⟨_, List.getElem?_eq_getElem Hlt⟩
      obtain ⟨q, hq⟩ : ∃ x, rr.perms[sint.nat n]? = some x :=
        ⟨_, List.getElem?_eq_getElem (by rw [← hzl']; exact Hlt)⟩
      have hz : (locs.zip rr.perms)[sint.nat n]? = some (lc, q) := by
        simp [List.getElem?_zip_eq_some, hlc, hq]
      wp_apply wp_load_slice_index kp (sint.Z n) locs (DFrac.own 1) lc Hn.1 $$ [Hkp] as Hkp
      · iframe; ipureintro; exact hlc
      ihave #Hq := Hpw $$ %(lc, q) %(List.mem_of_getElem? hz)
      (try wp_auto)
      wp_apply auth.wp_permW_key lc q $$ [$Hq] as %qk #Hqk
      (try wp_auto)
      wp_apply (_root_.Perennial.bytes.wp_Equal qk wk DFrac.discard DFrac.discard q.key w.key)
        $$ [$Hqk $Hwk] as ⟨-, -⟩
      have htake : (locs.zip rr.perms).take (sint.nat (n + W64 1)) =
          (locs.zip rr.perms).take (sint.nat n) ++ [(lc, q)] := by
        rw [show sint.nat (n + W64 1) = sint.nat n + 1 by word, List.take_add_one, hz]; rfl
      by_cases hk : q.key = w.key
      · rw [decide_eq_true hk]
        (try wp_auto)
        wp_apply auth.wp_permW_rangeEnd lc q $$ [$Hq] as %qre #Hqre
        (try wp_auto)
        wp_apply (_root_.Perennial.bytes.wp_Equal qre wre DFrac.discard DFrac.discard q.rangeEnd
          w.rangeEnd) $$ [$Hqre $Hwre] as ⟨-, -⟩
        by_cases hre : q.rangeEnd = w.rangeEnd
        · -- on `w`'s range: dropped
          have hoff : permWAt w.key w.rangeEnd q = true := by simp [permWAt, hk, hre]
          rw [decide_eq_true hre]
          (try wp_auto)
          wp_for_post
          iframe
          iexists n + W64 1, ks, kl, lc
          iframe
          ipureintro
          refine ⟨by word, by word, ?_⟩
          rw [htake, List.filter_append, Hn.2.2]
          simp [offW, hoff]
        · -- the same key, another range end: kept
          have hoff : permWAt w.key w.rangeEnd q = false := by simp [permWAt, hre]
          rw [decide_eq_false hre]
          (try wp_auto)
          wp_apply wp_slice_literal (V := Loc) [lc]
          isplitr
          · ipureintro; rfl
          iintro %sl1 ⟨Hsl1, -⟩
          (try wp_auto)
          wp_apply (wp_slice_append ks (kl.map Prod.fst) _ [lc] (DFrac.own 1)) $$ [$Hks $Hksc $Hsl1]
            as %s2 ⟨Hs2, Hs2c, -⟩
          (try wp_auto)
          wp_for_post
          iframe
          iexists n + W64 1, s2, kl ++ [(lc, q)], lc
          iframe
          isplitl [Hs2]
          · iExactEq Hs2; simp
          ipureintro
          refine ⟨by word, by word, ?_⟩
          rw [htake, List.filter_append, Hn.2.2]
          congr 1
          simp [offW, hoff]
      · -- another key: kept
        have hoff : permWAt w.key w.rangeEnd q = false := by simp [permWAt, hk]
        rw [decide_eq_false hk]
        (try wp_auto)
        wp_apply wp_slice_literal (V := Loc) [lc]
        isplitr
        · ipureintro; rfl
        iintro %sl1 ⟨Hsl1, -⟩
        (try wp_auto)
        wp_apply (wp_slice_append ks (kl.map Prod.fst) _ [lc] (DFrac.own 1)) $$ [$Hks $Hksc $Hsl1]
          as %s2 ⟨Hs2, Hs2c, -⟩
        (try wp_auto)
        wp_for_post
        iframe
        iexists n + W64 1, s2, kl ++ [(lc, q)], lc
        iframe
        isplitl [Hs2]
        · iExactEq Hs2; simp
        ipureintro
        refine ⟨by word, by word, ?_⟩
        rw [htake, List.filter_append, Hn.2.2]
        congr 1
        simp [offW, hoff]
    · -- the loop done: `kept` holds the permissions off `w`'s range
      have Hrl : rl ≠ null := by assumption
      have hnl : sint.nat n = locs.length := by have := Hkpl; word
      have hzlen : (locs.zip rr.perms).length = locs.length := by
        rw [List.length_zip, hzl', Nat.min_self]
      have hkept : kl.map Prod.snd = rr.perms.filter (fun q => !permWAt w.key w.rangeEnd q) := by
        rw [Hn.2.2, hnl, List.take_of_length_le (by omega)]
        have h2 : (List.filter offW (locs.zip rr.perms)).map Prod.snd =
            ((locs.zip rr.perms).map Prod.snd).filter (fun q => !permWAt w.key w.rangeEnd q) := by
          rw [List.filter_map]; rfl
        rw [h2, List.map_snd_zip (by omega)]
      have hklm : ∀ x, x ∈ kl → x ∈ locs.zip rr.perms := fun x h => by
        rw [Hn.2.2] at h; exact List.mem_of_mem_take (List.mem_filter.mp h).1
      have hkll : kl.length ≤ rr.perms.length := by
        rw [Hn.2.2]
        exact Nat.le_trans (List.length_filter_le _ _) (Nat.le_trans (List.length_take_le _ _) (by omega))
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
      wp_apply wp_slice_literal (V := Loc) [«$r0_ptr»]
      isplitr
      · ipureintro; rfl
      iintro %sl1 ⟨Hsl1, -⟩
      (try wp_auto)
      wp_apply (wp_slice_append ks (kl.map Prod.fst) _ [«$r0_ptr»] (DFrac.own 1)) $$ [$Hks $Hksc $Hsl1]
        as %s2 ⟨Hs2, Hs2c, -⟩
      (try wp_auto)
      ihave #Hsrt := auth.permSlice_isSorter s2 $$ Hpkg
      have hfst : (kl ++ [(«$r0_ptr», w)]).map Prod.fst = kl.map Prod.fst ++ [«$r0_ptr»] := by
        simp
      wp_apply (_root_.Perennial.sort.wp_Sort (interface.mk permSlice.ty #s2) (auth.permsOwn s2) keyLt
          StrictWeakOrder_keyLt (kl ++ [(«$r0_ptr», w)])) $$ [Hs2]
        as %xs' ⟨Hxs, %Hperm, %Hsorted⟩
      · iframe Hsrt
        isplitl [Hs2]
        · iunfold auth.permsOwn
          isplitl [Hs2]
          · iExactEq Hs2; rw [hfst]
          iintro !> %x %Hx
          rcases List.mem_append.mp Hx with h | h
          · iapply Hpw; ipureintro; exact hklm _ h
          · simp only [List.mem_singleton] at h; subst h; iexact Hnpw
        ipureintro
        rw [List.length_append]
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
        · iapply typedPointsto_combine rl _ _ Hrl
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
      have hstep : roleGrantPermissionR name (some w) st0
          (.next (bump (putRole st0 name (grantPerms ps w)))) := by
        simp [roleGrantPermissionR, hvalid, Hlook]
      have hkeys : M.isOn = true → M ≠ .any → ∀ p ∈ grantPerms ps w, p.key ≠ [] := fun h1 h2 =>
        auth.grant_keys ps w hvalid.1 (fun p hp => Hpk st0 Hl0 h1 h2 name ps Hlook p hp)
      have hgp := auth.grant_kept_perm rr ps w kl xs' «$r0_ptr» Hrrp hkept Hperm
      have hrn : ({ rr with perms := xs'.map Prod.snd } : RoleRec).name = name := Hrrn
      generalize ({ rr with perms := xs'.map Prod.snd } : RoleRec) = rr' at hgp hrn ⊢
      wp_bind (App (Val #(methods ti.ty go!"UnsafePutRole" ti.v)) (Val #rl))
      iapply HPutR $$ %st0 %Post %rl %rr' %(grantPerms ps w) [HL Hrm]
      · iframe HL Hrm; ipureintro; rw [hrn]; exact ⟨Hnamelen, hgp⟩
      inext
      iintro ⟨HL, Hrr⟩
      (try wp_auto)
      ihave HL : Lk (putRole st0 name (grantPerms ps w)) Post $$ [HL]
      · iExactEq HL; rw [hrn]
      obtain ⟨Hrevfit, Hfit⟩ := Hok st0 Hl0
      have Hfit' := Hfit _ _ hstep rfl
      ihave #Hcn := capNextM_use M hs _ st0 _ Hl0 hstep $$ Hcap
      wp_apply (h_commitRevision st R M P f T ti Lk (putRole st0 name (grantPerms ps w)) Post hs st0)
        $$ [$Hinv $HLk $HL $Hown $Hcn] as ⟨%rev, %Hrev, HL, Hown⟩
      · ipureintro
        refine ⟨Hl0, rfl, Hrevfit, fun h1 h2 =>
          permKeysOk_putRole _ _ _ (Hpk st0 Hl0 h1 h2) (hkeys h1 h2), ?_⟩
        intro hM; subst hM; exact Hl0
      have Hl1 := histLast_after M hs (putRole st0 name (grantPerms ps w)) rev
        (fun h => by subst h; exact Hl0) Hrev
      imod (authSnapF_of_last M _ _ Hl1) $$ Hown with ⟨Hown, #Hsnap⟩
      (try wp_auto)
      wp_bind (App (Val (st @!! go.GoType.PointerType authStore.ty @!! go!"refreshRangePermCache"))
        (Val #(GoInterface.ok ti)))
      iapply (h_refresh st R M ti (fun x => Lk x Post)
          ({ putRole st0 name (grantPerms ps w) with revision := rev } : AuthState) (hs ++ [bump (putRole st0 name (grantPerms ps w))]))
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
      irename «$r0» => Hresp
      generalize «$r0_ptr» = resp at *
      icases typedPointsto_split _ _ _ $$ Hresp with Hresp
      simp only [TypedPointsto.typedPointstoDef]
      iNamed Hresp
      (try wp_auto)
      wp_apply HUnlock $$ %_ %Post %(hs ++ [bump (putRole st0 name (grantPerms ps w))]) [HL $Hown]
        as ⟨HPost, HT, Hown⟩
      · isplitl [HL]
        · iExactEq HL
          all_goals rfl
        ipureintro; exact Hl1
      (try wp_auto)
      iapply HΦ
      iexists b0, ({ putRole st0 name (grantPerms ps w) with revision := rev } : AuthState)
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
      iexists st0, (.next (bump (putRole st0 name (grantPerms ps w))))
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
