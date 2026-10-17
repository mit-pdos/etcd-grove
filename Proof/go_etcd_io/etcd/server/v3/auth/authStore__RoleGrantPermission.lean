/-
Proof of `Spec/go_etcd_io/etcd/server/v3/auth/authStore__RoleGrantPermission.lean`. Lean-first
(no Rocq counterpart; PR etcd#21845, `pr-verify/etcd-21845`).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.auth.authStore__RoleGrantPermission
public import Spec.go_etcd_io.etcd.server.v3.auth.isValidPermissionRange
public import Spec.go_etcd_io.etcd.server.v3.auth.authStore__commitRevision
public import Spec.go_etcd_io.etcd.server.v3.auth.authStore__refreshRangePermCache
public import Spec.go_etcd_io.etcd.server.v3.auth.permSlice__Len
public import Spec.go_etcd_io.etcd.server.v3.auth.permSlice__Less
public import Spec.go_etcd_io.etcd.server.v3.auth.permSlice__Swap
public import Spec.go_uber_org.zap.String
public import Spec.go_uber_org.zap.ByteString
public import Spec.go_uber_org.zap.Logger__Info
public import Spec.sort.Sort
public import Perennial.Proof.bytes
public import Perennial.Proof.sort

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.auth go_etcd_io.etcd.api.v3 auth

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.auth.Assumptions]

/-- The keys' order on (pointer, permission) pairs is a strict weak order. -/
theorem auth.permKeyLt_swo :
    slices.StrictWeakOrder (fun a b : Loc × PermM => decide (keyLt a.2 b.2) = true) := by
  simp only [decide_eq_true_eq]
  exact keyLt_swo Prod.snd

/-- `permSlice` over the slice `sl` sorts the (pointer, permission) list of its permissions, by
key. -/
theorem auth.permSlice_sorter
    (hLen : auth.permSlice.Len.spec (GF := GF) (hG := hG))
    (hLess : auth.permSlice.Less.spec (GF := GF) (hG := hG))
    (hSwap : auth.permSlice.Swap.spec (GF := GF) (hG := hG)) (sl : GoSlice) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth ⊢
      sorterSpec (interface.mk permSlice.ty #sl) (ownPerms sl)
        (fun a b => decide (keyLt a.2 b.2)) := by
  iintro #Hpkg
  unfold sorterSpec
  isplitr
  · imodintro
    iintro %l
    iintro !> %Φ Hps HΦ
    iunfold ownPerms at Hps
    icases Hps with ⟨Hs, Hk⟩
    wp_apply (hLen sl (l.map Prod.fst) (DFrac.own 1)) $$ [$Hs] as Hs
    rw [List.length_map]
    iapply HΦ
    iunfold ownPerms
    iframe
  isplitr
  · imodintro
    iintro %l %i %j %a %b %Hij
    iintro !> %Φ Hps HΦ
    wp_apply (hLess sl l i j a b) $$ [$Hps] as Hps
    · ipureintro; exact Hij
    iapply HΦ
    iframe
  imodintro
  iintro %l %i %j %a %b %Hij
  iintro !> %Φ Hps HΦ
  iunfold ownPerms at Hps
  icases Hps with ⟨Hs, Hk⟩
  obtain ⟨hi, hj, ha, hb⟩ := Hij
  have hp : l.Perm ((l.set (sint.nat i) b).set (sint.nat j) a) :=
    slices.swap_perm l (sint.nat j) (sint.nat i) b a hb ha
  wp_apply (hSwap sl (l.map Prod.fst) i j a.1 b.1) $$ [$Hs] as Hs
  · ipureintro
    refine ⟨hi, hj, ?_, ?_⟩
    · rw [List.getElem?_map, ha]; rfl
    · rw [List.getElem?_map, hb]; rfl
  iapply HΦ
  iunfold ownPerms
  rw [List.map_set, List.map_set]
  iframe Hs
  iapply (BigSepL.bigSepL_perm (PROP := IProp GF)
    (Φ := fun (x : Loc × PermM) => ownPerm (GF := GF) x.1 x.2) hp).1
  iexact Hk

theorem auth.authStore.RoleGrantPermission.wp_proof
    (h_valid : auth.isValidPermissionRange.spec (GF := GF) (hG := hG))
    (h_commit : auth.authStore.commitRevision.spec (GF := GF) (hG := hG))
    (h_refresh : auth.authStore.refreshRangePermCache.spec (GF := GF) (hG := hG))
    (h_String : zap.String.spec (GF := GF) (hG := hG))
    (h_ByteString : zap.ByteString.spec (GF := GF) (hG := hG))
    (h_Info : zap.Logger.Info.spec (GF := GF) (hG := hG))
    (h_Sort : sort.«Sort».spec (GF := GF) (hG := hG))
    (h_Len : auth.permSlice.Len.spec (GF := GF) (hG := hG))
    (h_Less : auth.permSlice.Less.spec (GF := GF) (hG := hG))
    (h_Swap : auth.permSlice.Swap.spec (GF := GF) (hG := hG)) :
    auth.authStore.RoleGrantPermission.spec (GF := GF) (hG := hG) :=
    fun st R W H Roles m r name pp p => by
  wp_start as ⟨#Hinv, #Hwr, #Hglob, #Hreq, HW, HRoles, %Hm⟩
  ihave #Hzap : isPkgInit (PROP := IProp GF) pkg_id.go_uber_org.zap $$ []
  · iPkgInit
  ihave #Hbytes : isPkgInit (PROP := IProp GF) pkg_id.bytes $$ []
  · iPkgInit
  ihave #Hsort : isPkgInit (PROP := IProp GF) pkg_id.sort $$ []
  · iPkgInit
  ihave #Hinv' := Hinv
  iunfold authInv at Hinv'
  icases Hinv' with ⟨%Hst, -, ⟨%lg, #Hlg, %Hlgnn⟩, ⟨%be0, #Hbe0, -⟩, -, -, -⟩
  iunfold authWriteInv at Hwr
  icases Hwr with ⟨%be, #Hbe, #Hbeok⟩
  iunfold grantGlobals at Hglob
  icases Hglob with ⟨⟨%eNG, #HeNG, %HeNG0⟩, ⟨%eIM, #HeIM, %HeIM0⟩, ⟨%eRNF, #HeRNF, %HeRNF0⟩,
    ⟨%ptn, %PTN, #Hptn, #HPTN⟩⟩
  iunfold grantReqOk at Hreq
  icases Hreq with ⟨%rv, #Hr, %Hrv, Hpp⟩
  obtain ⟨Hrn, Hrp⟩ := Hrv
  wp_apply wp_with_defer as %defer defer
  (try wp_auto)
  iStructNamed Hr
  wp_auto
  rw [Hrp]
  wp_if_destruct
  · -- no permission: `ErrPermissionNotGiven`
    iapply HΦ
    iframe HW
    iexists m
    iframe HRoles
    ipureintro
    exact ⟨Hm.1, fun h => absurd h HeNG0, fun _ => rfl, fun _ => HeNG0⟩
  icases Hpp with ⟨%Hnull | ⟨%Hnn, #Hpm⟩⟩
  · exact absurd Hnull Hif
  iunfold permRO at Hpm
  icases Hpm with ⟨%pv, #Hpv, %Hpvt, #Hpk, #Hpre⟩
  iStructNamedPrefix Hpv "pv"
  wp_auto
  wp_apply (h_valid pv.Key' pv.RangeEnd' p.key p.rangeEnd DFrac.discard DFrac.discard) $$ []
    as %okr -
  · iframe #
  cases okr
  · -- an invalid range: `ErrInvalidAuthMgmt`
    wp_auto
    iapply HΦ
    iframe HW
    iexists m
    iframe HRoles
    ipureintro
    exact ⟨Hm.1, fun h => absurd h HeIM0, fun _ => rfl, fun _ => HeIM0⟩
  wp_auto
  icombine Hbe Hbe0 gives %Hbeq
  iunfold authWriteBackendOk at Hbeok
  icases Hbeok with ⟨%bi, %Hbi, #HBT⟩
  subst Hbi
  wp_auto
  wp_apply HBT as %tx #Htx
  ihave #Htx' := Htx
  iunfold authBatchTxOk at Htx
  icases Htx with ⟨%ti, %Hti, #HLock, #HUnlock, #HGet, #HPut⟩
  subst Hti
  wp_auto
  wp_bind (App (Val #(methods ti.ty go!"Lock" ti.v)) (Val #()))
  iapply HLock $$ HW
  inext
  iintro Htok
  wp_auto
  rw [Hrn]
  wp_bind (App (Val #(methods ti.ty go!"UnsafeGetRole" ti.v)) (Val #name))
  iapply HGet $$ [$Htok $HRoles]
  inext
  iintro %rp ⟨Htok, HRoles, Hrole⟩
  wp_auto
  iunfold roleIs at Hrole
  icases Hrole with ⟨⟨%Hrpn, %Hmn⟩ | ⟨%ps, ⟨%Hrpnn, %Hmn⟩, Hrole⟩⟩
  · -- no role: `ErrRoleNotFound`
    subst Hrpn
    wp_auto
    wp_bind (App (Val #(methods ti.ty go!"Unlock" ti.v)) (Val #()))
    iapply HUnlock $$ Htok
    inext
    iintro HW
    wp_auto
    iapply HΦ
    iframe HW
    iexists m
    iframe HRoles
    ipureintro
    exact ⟨Hm.1, fun h => absurd h HeRNF0, fun _ => rfl, fun _ => HeRNF0⟩
  wp_if_destruct
  · exact absurd rfl Hrpnn
  iunfold ownRole at Hrole
  icases Hrole with ⟨%rv0, %l, Hrv, #Hname, Hps, Hcap, %Hlps⟩
  iunfold ownPerms at Hps
  icases Hps with ⟨Hsl, Hms⟩
  ihave %Hsll := ownSlice_len _ _ _ $$ Hsl
  simp only [List.length_map] at Hsll
  have hpsl : ps.length = l.length := by rw [← Hlps, List.length_map]
  have Hsorted : SortedByKey ps := Hm.1 name ps Hmn
  wp_auto
  wp_func_lits
  wp_apply sort.wp_Search rv0.KeyPermission'.len _ (keyGe ps p.key)
    iprop(role_ptr ↦ rp ∗ r_ptr ↦ r ∗ rp ↦ rv0 ∗ rv0.KeyPermission' ↦* l.map Prod.fst ∗
      [∗list] x ∈ l, ownPerm x.1 x.2)
    $$ [role r Hrv Hsl Hms]
  · iframe
    isplitl []
    · ipureintro; exact Hsll.2
    isplitl []
    · unfold sort.predImplements
      iintro %i
      iclear HBT HLock HUnlock HGet HPut Htx'
      wp_start as ⟨⟨role, r, Hrv, Hsl, Hms⟩, %Hb⟩
      wp_auto
      have hil : sint.nat i < l.length := by have := Hsll.1; word
      try simp only [Hb, _root_.and_self, ite_true]
      list_elem l (sint.nat i) as x
      wp_apply wp_load_slice_index _ (sint.Z i) _ (DFrac.own 1) x.1 Hb.1 $$ [Hsl] as Hsl
      · iframe; ipureintro; rw [List.getElem?_map]; exact congrArg (Option.map Prod.fst) Hx_lookup
      icases auth.ownPerms_acc l (sint.nat i) x Hx_lookup $$ Hms with ⟨Hx, Hclose⟩
      iunfold ownPerm at Hx
      icases Hx with ⟨%xv, Hxv, %Hxpt, #Hxk, #Hxre⟩
      wp_auto
      ihave Hms := Hclose $$ [Hxv]
      · iunfold ownPerm; iexists xv; iframe; iframe #; ipureintro; exact Hxpt
      wp_apply (bytes.wp_Compare _ _ DFrac.discard DFrac.discard x.2.key p.key) $$ [] as ⟨-, -⟩
      · iframe #
      rw [compareResult_ge]
      iapply HΦ
      iframe
      ipureintro
      unfold keyGe
      have hx2 : ps[sint.nat i]? = some x.2 := by
        rw [← Hlps, List.getElem?_map, Hx_lookup]; rfl
      rw [show (sint.Z i).toNat = sint.nat i from rfl, hx2]
      simp only [decide_not]
    · ipureintro
      have := keyGe_mono Hsorted p.key
      intro a b hab
      apply this a b
      have := Hsll.1; refine ⟨hab.1, hab.2.1, ?_⟩; rw [hpsl]; word
  iintro %idx ⟨⟨role, r, Hrv, Hsl, Hms⟩, %Hidx0, %Hfound, %Hoob, %Hlow⟩
  have Hidx_le : sint.Z idx ≤ sint.Z rv0.KeyPermission'.len := by
    apply Classical.byContradiction
    intro h
    have := Hoob (fun i hi => Hlow i ⟨hi.1, by omega⟩)
    omega
  have Hbefore : ∀ (k : Nat) (q : PermM), k < sint.nat idx → ps[k]? = some q →
      go.GoStringLt q.key p.key := by
    intro k q hk hq
    have := Hlow k ⟨by omega, by word⟩
    unfold keyGe at this
    rw [show ((k : Int)).toNat = k by omega, hq] at this
    simpa using this
  wp_auto
  wp_join iprop(∃ ev : w64, existing_ptr ↦ ev ∗ role_ptr ↦ rp ∗ r_ptr ↦ r ∗ rp ↦ rv0 ∗
      rv0.KeyPermission' ↦* l.map Prod.fst ∗ ([∗list] x ∈ l, ownPerm x.1 x.2) ∗
      ⌜ExistingOk ps p (sint.Z ev)⌝) at next with [existing i role r Hrv Hsl Hms]
    as ⟨%ev, existing, role, r, Hrv, Hsl, Hms, %Hex⟩
  · ihave HI : (∃ iv : w64, "i" ∷ i_ptr ↦ iv ∗
        "%Hiv" ∷ ⌜sint.Z idx ≤ sint.Z iv ∧ sint.Z iv ≤ sint.Z rv0.KeyPermission'.len ∧
          ∀ (k : Nat) (q : PermM), sint.nat idx ≤ k → k < sint.nat iv → ps[k]? = some q →
            q.key = p.key ∧ q.rangeEnd ≠ p.rangeEnd⌝ : IProp GF) $$ [i]
    · iexists idx
      iframe
      ipureintro
      refine ⟨Int.le_refl _, Hidx_le, fun k q h1 h2 _ => by omega⟩
    wp_for HI
    wp_if_destruct
    · -- `i < len(role.KeyPermission)`
      have Hbi : 0 ≤ sint.Z iv ∧ sint.Z iv < sint.Z rv0.KeyPermission'.len := ⟨by omega, Hif⟩
      have hil : sint.nat iv < l.length := by have := Hsll.1; word
      try simp only [Hbi, _root_.and_self, ite_true]
      list_elem l (sint.nat iv) as x
      have hx2 : ps[sint.nat iv]? = some x.2 := by
        rw [← Hlps, List.getElem?_map, Hx_lookup]; rfl
      wp_apply wp_load_slice_index _ (sint.Z iv) _ (DFrac.own 1) x.1 Hbi.1 $$ [Hsl] as Hsl
      · iframe; ipureintro; rw [List.getElem?_map]; exact congrArg (Option.map Prod.fst) Hx_lookup
      icases auth.ownPerms_acc l (sint.nat iv) x Hx_lookup $$ Hms with ⟨Hx, Hclose⟩
      iunfold ownPerm at Hx
      icases Hx with ⟨%xv, Hxv, %Hxpt, #Hxk, #Hxre⟩
      wp_auto
      wp_apply (bytes.wp_Equal _ _ DFrac.discard DFrac.discard x.2.key p.key) $$ [] as ⟨-, -⟩
      · iframe #
      wp_if_destruct
      · -- the same key: compare the range ends
        have hkey : x.2.key = p.key := by
          have h := ‹#(decide (x.2.key = p.key)) = #true›
          simp only [intoVal_eq_iff, decide_eq_true_eq] at h; exact h
        try simp only [Hbi, _root_.and_self, ite_true]
        wp_apply wp_load_slice_index _ (sint.Z iv) _ (DFrac.own 1) x.1 Hbi.1 $$ [Hsl] as Hsl
        · iframe; ipureintro; rw [List.getElem?_map]; exact congrArg (Option.map Prod.fst) Hx_lookup
        wp_apply (bytes.wp_Equal _ _ DFrac.discard DFrac.discard x.2.rangeEnd p.rangeEnd) $$ []
          as ⟨-, -⟩
        · iframe #
        ihave Hms := Hclose $$ [Hxv]
        · iunfold ownPerm; iexists xv; iframe; iframe #; ipureintro; exact Hxpt
        wp_if_destruct
        · -- found: `existing = i; break`
          wp_for_post
          isplitl []
          · ipureintro; rfl
          iexists iv
          iframe
          ipureintro
          right
          refine ⟨Hbi.1, x.2, hx2, ⟨hkey, ‹_›⟩, ?_⟩
          exact scan_below Hbefore (fun k q h1 h2 h3 => Hiv.2.2 k q h1 h2 h3)
        · -- another range end: next
          have hre : ¬ x.2.rangeEnd = p.rangeEnd := ‹_›
          wp_for_post
          iframe
          iexists iv + W64 1
          iframe
          ipureintro
          refine ⟨by word, by word, ?_⟩
          intro k q h1 h2 h3
          by_cases hk : k < sint.nat iv
          · exact Hiv.2.2 k q h1 hk h3
          · have hkv : k = sint.nat iv := by
              have : sint.nat (iv + W64 1) = sint.nat iv + 1 := by word
              omega
            subst hkv
            rw [hx2] at h3; injection h3 with h3; subst h3
            exact ⟨hkey, hre⟩
      · -- another key: the scan ends
        have hkey : ¬ x.2.key = p.key := by
          have h := ‹¬ #(decide (x.2.key = p.key)) = #true›
          simp only [intoVal_eq_iff, decide_eq_true_eq] at h; exact h
        ihave Hms := Hclose $$ [Hxv]
        · iunfold ownPerm; iexists xv; iframe; iframe #; ipureintro; exact Hxpt
        rw [_root_.decide_eq_false hkey]
        simp only [Bool.false_eq_true, ↓reduceIte]
        isplitl []
        · ipureintro; trivial
        iexists W64 (-1)
        iframe
        ipureintro
        left
        refine ⟨by decide, ?_⟩
        apply scan_none Hsorted (sint.nat iv)
          (scan_below Hbefore (fun k q h1 h2 h3 => Hiv.2.2 k q h1 h2 h3))
        right
        refine ⟨x.2, hx2, ?_, hkey⟩
        have hge : keyGe ps p.key (sint.Z iv) = true := by
          by_cases hie : sint.Z iv = sint.Z idx
          · rw [hie]; exact Hfound (by omega)
          · exact keyGe_mono Hsorted p.key (sint.Z idx) (sint.Z iv)
              ⟨Hidx0, by omega, by rw [hpsl]; have := Hsll.1; word⟩ (Hfound (by omega))
        unfold keyGe at hge
        rw [show (sint.Z iv).toNat = sint.nat iv from rfl, hx2] at hge
        simpa using hge
    · -- the end of the permissions
      isplitl []
      · ipureintro; trivial
      iexists W64 (-1)
      iframe
      ipureintro
      left
      refine ⟨by decide, ?_⟩
      apply scan_none Hsorted (sint.nat iv)
        (scan_below Hbefore (fun k q h1 h2 h3 => Hiv.2.2 k q h1 h2 h3))
      left
      rw [hpsl, Hsll.1]; word
  wp_join iprop(∃ ps' : List PermM, role_ptr ↦ rp ∗ r_ptr ↦ r ∗ ownRole rp name ps' ∗
      ⌜GrantSpec ps ps' p⌝) with [existing role r Hrv Hsl Hms Hcap] as ⟨%ps', role, r, Hrole, %Hgrant⟩
  · -- a permission on `p`'s range at `existing`: update its type
    have Hex' : 0 ≤ sint.Z ev ∧ ∃ q, ps[(sint.Z ev).toNat]? = some q ∧ sameRange q p ∧
        ∀ (k : Nat) (q' : PermM), k < (sint.Z ev).toNat → ps[k]? = some q' → ¬ sameRange q' p := by
      rcases Hex with ⟨h, _⟩ | h
      · have h0 := ‹sint.Z (W64 0) ≤ sint.Z ev›; rw [h] at h0; exact absurd h0 (by decide)
      · exact h
    obtain ⟨hev0, q, hq, hqr, hqfirst⟩ := Hex'
    have hevl : sint.nat ev < l.length := by
      rw [← hpsl]; exact (List.getElem?_eq_some_iff.1 hq).1
    have Hbe : 0 ≤ sint.Z ev ∧ sint.Z ev < sint.Z rv0.KeyPermission'.len := by
      have := Hsll.1; refine ⟨hev0, ?_⟩; word
    try simp only [Hbe, _root_.and_self, ite_true]
    list_elem l (sint.nat ev) as y
    have hy2 : y.2 = q := by
      have : ps[sint.nat ev]? = some y.2 := by rw [← Hlps, List.getElem?_map, Hy_lookup]; rfl
      rw [show (sint.Z ev).toNat = sint.nat ev from rfl, this] at hq; injection hq
    wp_apply wp_load_slice_index _ (sint.Z ev) _ (DFrac.own 1) y.1 Hbe.1 $$ [Hsl] as Hsl
    · iframe; ipureintro; rw [List.getElem?_map]; exact congrArg (Option.map Prod.fst) Hy_lookup
    icases (BigSepL.bigSepL_insert_acc (PROP := IProp GF)
      (Φ := fun (_ : Nat) (z : Loc × PermM) => ownPerm (GF := GF) z.1 z.2) Hy_lookup) $$ Hms
      with ⟨Hy, Hclose⟩
    iunfold ownPerm at Hy
    icases Hy with ⟨%yv, Hyv, %Hypt, #Hyk, #Hyre⟩
    wp_auto
    ihave Hms := Hclose $$ %(y.1, p) [Hyv]
    · have hk : p.key = y.2.key := by rw [hy2]; exact hqr.1.symm
      have hre : p.rangeEnd = y.2.rangeEnd := by rw [hy2]; exact hqr.2.symm
      iunfold ownPerm
      iexists _
      iframe Hyv
      simp only
      rw [hk, hre]
      iframe #
      ipureintro; exact Hpvt
    wp_join_done
    iexists ps.set (sint.nat ev) p
    iframe
    isplitl
    · iunfold ownRole
      iexists rv0, l.set (sint.nat ev) (y.1, p)
      iframe #
      iunfold ownPerms
      have hsetfst : (l.set (sint.nat ev) (y.1, p)).map Prod.fst = l.map Prod.fst := by
        rw [List.map_set]
        exact list_set_lookup_self (l.map Prod.fst) (sint.nat ev) y.1
          (by rw [List.getElem?_map, Hy_lookup]; rfl)
      rw [hsetfst]
      iframe
      ipureintro
      rw [List.map_set, Hlps]
    ipureintro
    left
    exact ⟨sint.nat ev, q, hq, hqr, hqfirst, rfl⟩
  · -- none: append `p` and sort
    have Hnone : ∀ q ∈ ps, ¬ sameRange q p := by
      rcases Hex with ⟨_, h⟩ | ⟨h, _⟩
      · exact h
      · exact absurd h (by have := ‹¬ sint.Z (W64 0) ≤ sint.Z ev›; word)
    irename «$r0» => Hnp
    wp_apply wp_slice_literal (V := Loc) [«$r0_ptr»]
    isplitr
    · ipureintro; rfl
    iintro %sl2 ⟨Hsl2, -⟩
    (try wp_auto)
    wp_apply wp_slice_append (V := Loc) _ _ _ _ _ $$ [$Hsl $Hcap $Hsl2] as %sl3 ⟨Hsl, Hcap, -⟩
    (try wp_auto)
    ihave #Hsorter := auth.permSlice_sorter h_Len h_Less h_Swap sl3 $$ Hpkg
    have hlen : (l ++ [(«$r0_ptr», p)]).length ≤ 2 ^ 62 := by
      have := Hm.2 ps Hmn; rw [hpsl] at this; simp only [List.length_append, List.length_cons,
        List.length_nil]; omega
    wp_apply (h_Sort (Loc × PermM) _ (ownPerms sl3) (fun a b => decide (keyLt a.2 b.2))
        (l ++ [(«$r0_ptr», p)]) auth.permKeyLt_swo) $$ [Hsl Hms Hnp] as %l' ⟨Hps, %Hsrt⟩
    · iframe #
      iunfold ownPerms
      simp only [List.map_append, List.map_cons, List.map_nil]
      iframe Hsl
      isplitl
      · iapply BigSepL.bigSepL_snoc.2
        iframe Hms
        iunfold ownPerm
        iexists _
        iframe Hnp
        iframe #
        ipureintro; simp only; exact Hpvt
      ipureintro; exact hlen
    wp_join_done
    iexists l'.map Prod.snd
    iframe
    isplitl
    · iunfold ownRole
      iexists _, l'
      iframe
      iframe #
      isplitl [Hps]
      · iexact Hps
      ipureintro; rfl
    ipureintro
    right
    refine ⟨Hnone, ?_, ?_⟩
    · have := (Hsrt.1.map Prod.snd).symm
      rw [List.map_append, Hlps] at this
      exact this
    · intro a b x y ha hb hab
      rw [List.getElem?_map] at ha hb
      cases ha' : l'[a]? <;> rw [ha'] at ha <;> simp at ha
      cases hb' : l'[b]? <;> rw [hb'] at hb <;> simp at hb
      have := Hsrt.2 a b _ _ ha' hb' hab
      subst ha hb
      simpa using this
  wp_bind (App (Val #(methods ti.ty go!"UnsafePutRole" ti.v)) (Val #rp))
  iapply HPut $$ [$Htok $HRoles $Hrole]
  inext
  iintro ⟨Htok, HRoles, Hrole⟩
  wp_auto
  wp_apply (h_commit st R W H Roles (GoInterface.ok ti)) $$ [$Htok] as Htok
  · iframe #
  wp_apply (h_refresh st R W H Roles (rolesSet m name ps') (GoInterface.ok ti)) $$ [$Htok $HRoles]
    as ⟨Htok, HRoles⟩
  · iframe #
  wp_apply h_String _ _ as %f1 -
  (try wp_auto)
  wp_apply (wp_map_lookup1 go.int32 go.string ptn PTN pv.PermType' DFrac.discard) $$ []
    as -
  · iframe #
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
  wp_alloc resp as Hresp
  wp_auto
  wp_bind (App (Val #(methods ti.ty go!"Unlock" ti.v)) (Val #()))
  iapply HUnlock $$ Htok
  inext
  iintro HW
  wp_auto
  iapply HΦ
  iframe HW
  iexists rolesSet m name ps'
  iframe HRoles
  ipureintro
  refine ⟨?_, fun _ => ⟨Hnn, ps, ps', Hmn, Hgrant, rfl⟩, fun h => absurd rfl h, fun h => ?_⟩
  · intro n qs hn
    unfold rolesSet at hn
    split at hn
    · injection hn with hn; subst hn
      exact grantSpec_sorted Hsorted Hgrant
    · exact Hm.1 n qs hn
  · rw [Hmn] at h; cases h

end proof

end EtcdGrove
end Perennial
