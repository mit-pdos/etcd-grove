/-
`WriteInodeToPage`'s proof (`internal/common/inode.go`): a stub, proved by U1 of
`notes/bbolt-proof-plan.md`.
-/
module

public import Spec.go_etcd_io.bbolt.internal.common.WriteInodeToPage
public import Proof.go_etcd_io.bbolt.internal.common.Lemmas.Bytes
public import Proof.go_etcd_io.bbolt.internal.common.Lemmas.PageBody
public import Spec.go_etcd_io.bbolt.internal.common.Assert
public import Spec.go_etcd_io.bbolt.internal.common.Inode__Pgid
public import Spec.go_etcd_io.bbolt.internal.common.Inode__Flags
public import Spec.go_etcd_io.bbolt.internal.common.Inode__Value
public import Spec.go_etcd_io.bbolt.internal.common.Inode__Key
public import Spec.go_etcd_io.bbolt.internal.common.branchPageElement__Pgid
public import Spec.go_etcd_io.bbolt.internal.common.branchPageElement__SetPgid
public import Spec.go_etcd_io.bbolt.internal.common.branchPageElement__SetKsize
public import Spec.go_etcd_io.bbolt.internal.common.branchPageElement__SetPos
public import Spec.go_etcd_io.bbolt.internal.common.leafPageElement__SetVsize
public import Spec.go_etcd_io.bbolt.internal.common.leafPageElement__SetKsize
public import Spec.go_etcd_io.bbolt.internal.common.leafPageElement__SetFlags
public import Spec.go_etcd_io.bbolt.internal.common.leafPageElement__SetPos
public import Spec.go_etcd_io.bbolt.internal.common.Page__Id
public import Spec.go_etcd_io.bbolt.internal.common.Page__BranchPageElement
public import Spec.go_etcd_io.bbolt.internal.common.Page__LeafPageElement
public import Spec.go_etcd_io.bbolt.internal.common.Page__IsLeafPage
public import Spec.go_etcd_io.bbolt.internal.common.Page__PageElementSize
public import Spec.go_etcd_io.bbolt.internal.common.UnsafeByteSlice

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

namespace internal
namespace common

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt.internal.common

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.internal.common.Assumptions]

theorem WriteInodeToPage.wp_proof
    (wp_UnsafeByteSlice : UnsafeByteSlice.spec (GF := GF) (hG := hG))
    (wp_Page_PageElementSize : Page.PageElementSize.spec (GF := GF) (hG := hG))
    (wp_Page_IsLeafPage : Page.IsLeafPage.spec (GF := GF) (hG := hG))
    (wp_Page_LeafPageElement : Page.LeafPageElement.spec (GF := GF) (hG := hG))
    (wp_Page_BranchPageElement : Page.BranchPageElement.spec (GF := GF) (hG := hG))
    (wp_Page_Id : Page.Id.spec (GF := GF) (hG := hG))
    (wp_leafPageElement_SetPos : leafPageElement.SetPos.spec (GF := GF) (hG := hG))
    (wp_leafPageElement_SetFlags : leafPageElement.SetFlags.spec (GF := GF) (hG := hG))
    (wp_leafPageElement_SetKsize : leafPageElement.SetKsize.spec (GF := GF) (hG := hG))
    (wp_leafPageElement_SetVsize : leafPageElement.SetVsize.spec (GF := GF) (hG := hG))
    (wp_branchPageElement_SetPos : branchPageElement.SetPos.spec (GF := GF) (hG := hG))
    (wp_branchPageElement_SetKsize : branchPageElement.SetKsize.spec (GF := GF) (hG := hG))
    (wp_branchPageElement_SetPgid : branchPageElement.SetPgid.spec (GF := GF) (hG := hG))
    (wp_branchPageElement_Pgid : branchPageElement.Pgid.spec (GF := GF) (hG := hG))
    (wp_Inode_Key : Inode.Key.spec (GF := GF) (hG := hG))
    (wp_Inode_Value : Inode.Value.spec (GF := GF) (hG := hG))
    (wp_Inode_Flags : Inode.Flags.spec (GF := GF) (hG := hG))
    (wp_Inode_Pgid : Inode.Pgid.spec (GF := GF) (hG := hG))
    (wp_Assert : Assert.spec (GF := GF) (hG := hG)) :
    WriteInodeToPage.spec (GF := GF) (hG := hG) := by
  intro s ins ms dqs qk qv p hdr rest Hp0 Hfits Hrest Hcirc
  wp_start as ⟨Hs, Hins, Hp, Hb⟩
  obtain ⟨Hn16, Hfit, Hkeys⟩ := Hfits
  ihave %Hlen := BigSepL2.bigSepL2_length $$ Hins
  ihave %Hslen := ownSlice_len _ _ _ $$ Hs
  icases typedPointsto_not_null_dup _ _ _ $$ Hp with ⟨Hp, %Hpnn⟩
  wp_auto
  wp_apply wp_Page_PageElementSize $$ [$Hp] as Hp
  wp_apply wp_Page_IsLeafPage $$ [$Hp] as Hp
  rename_i k_ptr
  irename : k_ptr ↦ (zero_val w64) => Hk
  have hbody := pageBody_length true ms
  have hlenW : s.len = W64 (ms.length : Int) := by
    rw [← Hlen]; exact w64_of_sint_nat _ _ Hslen.1 Hslen.2
  have hsZ : sint.Z s.len = ms.length := by rw [hlenW]; exact sint_Z_W64_nat _ (by omega)
  -- the bytes after the header: the elements' region, then the data area
  ihave Hb : bytesPointsto (p +ₗ 16) (DFrac.own 1)
      (rest.take (16 * ms.length) ++ rest.drop (16 * ms.length)) $$ [Hb]
  · rw [List.take_append_drop]; iexact Hb
  icases (bytesPointsto_app _ _ _ _).1 $$ Hb with ⟨HE, HD⟩
  rw [List.length_take, Nat.min_eq_left (by omega), loc_add_assoc]
  generalize hleaf : decide (hdr.flags' = W16 2) = leaf at *
  ihave HI : (∃ (j kv : w64),
      "i" ∷ i_ptr ↦ j ∗
      "Hk" ∷ k_ptr ↦ kv ∗
      "off" ∷ off_ptr ↦ W64 (dataOff ms (sint.nat j) : Int) ∗
      "Hp" ∷ p ↦ hdr ∗
      "HE" ∷ bytesPointsto (p +ₗ 16) (DFrac.own 1)
        (elemsPrefix leaf ms (sint.nat j) ++
          (rest.drop (16 * sint.nat j)).take (16 * (ms.length - sint.nat j))) ∗
      "HD" ∷ bytesPointsto (p +ₗ ((16 : Int) + ((16 * ms.length : Nat) : Int))) (DFrac.own 1)
        (dataBytes (ms.take (sint.nat j)) ++
          (rest.drop (16 * ms.length)).drop (dataBytes (ms.take (sint.nat j))).length) ∗
      "Hs" ∷ s ↦*{dqs} ins ∗
      "Hins" ∷ ([∗list] k ↦ it;m ∈ ins;ms, ⌜it.flags' = m.flags ∧ it.pgid' = m.pgid⌝ ∗
        it.key' ↦*{qk k} m.key ∗ it.value' ↦*{qv k} m.value) ∗
      "HΦ" ∷ (s ↦*{dqs} ins ∗
        ([∗list] k ↦ it;m ∈ ins;ms, ⌜it.flags' = m.flags ∧ it.pgid' = m.pgid⌝ ∗
          it.key' ↦*{qk k} m.key ∗ it.value' ↦*{qv k} m.value) ∗ p ↦ hdr ∗
        bytesPointsto (p +ₗ 16) (DFrac.own 1) (pageBody leaf ms ++ rest.drop (pageBody true ms).length) -∗
        Φ #(W32 ((16 + (pageBody leaf ms).length : Nat) : Int))) ∗
      "«$res0»" ∷ «$res0_ptr» ↦ zero_val w32 ∗
      "p" ∷ p_ptr ↦ p ∗
      "isLeaf" ∷ isLeaf_ptr ↦ leaf ∗
      "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ ms.length⌝ : IProp GF)
    $$ [i Hk off Hp HE HD Hs Hins HΦ «$res0» p isLeaf]
  · iexists (W64 0), (zero_val w64 : w64)
    have h0 : sint.nat (W64 0) = 0 := rfl
    rw [h0, elemsPrefix_zero, List.take_zero, show dataBytes [] = [] from rfl, List.nil_append,
      List.nil_append, List.length_nil, Nat.sub_zero, Nat.mul_zero, List.drop_zero, List.drop_zero,
      dataOff_zero, hlenW, show W64 16 + W64 16 * W64 (ms.length : Int) =
        W64 ((16 + 16 * ms.length : Nat) : Int) by push_cast; word]
    iframe
    ipureintro; refine ⟨by decide, ?_⟩; simp
  wp_for HI
  have hjZ : sint.Z j = (sint.nat j : Int) := by
    simp only [sint.nat]; rw [Int.toNat_of_nonneg Hj.1]
  by_cases hexit : sint.Z j < sint.Z s.len
  · rw [decide_eq_true hexit]
    simp only [↓reduceIte]
    rw [hsZ] at hexit
    have hjn : sint.nat j < ms.length := by omega
    obtain ⟨x, hx⟩ : ∃ x, ins[sint.nat j]? = some x :=
      ⟨_, List.getElem?_eq_getElem (by omega)⟩
    have hm : ms[sint.nat j]? = some ms[sint.nat j] := List.getElem?_eq_getElem hjn
    have hle := dataOff_le ms (sint.nat j) hjn
    have hsucc := dataOff_succ ms (sint.nat j) hjn
    have hdsucc := dataBytes_take_succ ms (sint.nat j) hjn
    have hdge := dataOff_ge ms (sint.nat j)
    have hkne := Hkeys _ (List.getElem_mem hjn)
    have hcircj : leaf = false → ms[sint.nat j].pgid ≠ hdr.id' := by
      intro hl; refine Hcirc ?_ _ (List.getElem_mem hjn)
      intro h; rw [decide_eq_true h, hl] at hleaf; exact Bool.noConfusion hleaf
    have hDl := dataBytes_length_le ms (sint.nat j + 1)
    rw [hdsucc, List.length_append] at hDl
    have hstep := dataArea_step ms (rest.drop (16 * ms.length)) (sint.nat j) hjn
    generalize ms[sint.nat j] = m at hm hle hsucc hdsucc hkne hcircj hDl hstep
    ihave Hx := BigSepL2.bigSepL2_lookup_acc hx hm $$ Hins
    icases Hx with ⟨⟨%Hxfp, Hkey, Hval⟩, Hins⟩
    ihave %Hkl := ownSlice_len _ _ _ $$ Hkey
    ihave %Hvl := ownSlice_len _ _ _ $$ Hval
    wp_auto
    rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨Hj.1, by rw [hsZ]; omega⟩)]
    wp_apply wp_load_slice_index s (sint.Z j) ins dqs x Hj.1 $$ [Hs] as Hs
    · iframe Hs; ipureintro; rw [show (sint.Z j).toNat = sint.nat j from rfl]; exact hx
    -- the inode's key and value lengths
    have hkW : x.key'.len = W64 (m.key.length : Int) := w64_of_sint_nat _ _ Hkl.1 Hkl.2
    have hvW : x.value'.len = W64 (m.value.length : Int) := w64_of_sint_nat _ _ Hvl.1 Hvl.2
    have hkv : (m.key ++ m.value).length = m.key.length + m.value.length := by simp
    have hkpos : 0 < m.key.length := List.length_pos_iff.2 hkne
    have hDle : 16 + 16 * ms.length + (dataBytes (ms.take (sint.nat j))).length +
        (m.key ++ m.value).length ≤ 16 + (pageBody true ms).length := by
      simp only [dataOff, InodeM.kv] at hle; simp only [List.length_append]; omega
    ihave %Hbd := bytesPointsto_in_bounds_imp _ _ _ $$ HD
    have hbd : p.addr + 16 + rest.length ≤ maxAddr := by
      have := (Hbd (by
        intro h; have := congrArg List.length h
        simp only [List.length_append, List.length_drop, List.length_nil] at this; omega)).2
      simp only [Loc.add, List.length_append, List.length_drop] at this; omega
    have hkZ : sint.Z (W64 (m.key.length : Int)) = m.key.length := sint_Z_W64_nat _ (by omega)
    wp_apply wp_Inode_Key $$ [$item] as item
    rw [hkW, decide_eq_true (show sint.Z (W64 0) < sint.Z (W64 (m.key.length : Int)) by
      rw [hkZ, show sint.Z (W64 0) = 0 from rfl]; omega)]
    wp_apply wp_Assert
    wp_apply wp_Inode_Key $$ [$item] as item
    wp_apply wp_Inode_Value $$ [$item] as item
    have hszW : x.key'.len + x.value'.len = W64 ((m.key ++ m.value).length : Int) := by
      rw [hkW, hvW, hkv]; push_cast; word
    rw [hszW]
    have hdo : dataOff ms (sint.nat j) =
        16 + 16 * ms.length + (dataBytes (ms.take (sint.nat j))).length := rfl
    have hoffZ : sint.Z (W64 (dataOff ms (sint.nat j) : Int)) = dataOff ms (sint.nat j) :=
      sint_Z_W64_nat _ (by omega)
    have hszZ : sint.Z (W64 ((m.key ++ m.value).length : Int)) = (m.key ++ m.value).length :=
      sint_Z_W64_nat _ (by omega)
    wp_apply wp_UnsafeByteSlice
    · ipureintro; rw [hoffZ]; simp only [Loc.add]; omega
    · ipureintro; rw [hoffZ, hszZ]; simp only [Loc.add]; omega
    · ipureintro; decide
    · ipureintro; rw [hszZ, show sint.Z (W64 0) = 0 from rfl]; omega
    rw [hoffZ, show sint.Z (W64 0) = 0 from rfl, loc_add_0,
      show W64 ((m.key ++ m.value).length : Int) - W64 0 = W64 ((m.key ++ m.value).length : Int) by
        simp]
    wp_apply wp_Page_PageElementSize $$ [$Hp] as Hp
    have hmj : ms[sint.nat j] = m := by
      rw [List.getElem?_eq_getElem hjn] at hm; exact Option.some.inj hm
    have hjW64 : j = W64 ((sint.nat j : Nat) : Int) := w64_of_sint_nat j _ rfl Hj.1
    have hposW : W32 (uint.Z (W64 (dataOff ms (sint.nat j) : Int) - (W64 16 + W64 16 * j))) =
        W32 ((dataOff ms (sint.nat j) - (16 + 16 * sint.nat j) : Nat) : Int) := by
      have h1 : 16 + 16 * sint.nat j ≤ dataOff ms (sint.nat j) := by omega
      have h2 : dataOff ms (sint.nat j) < 2 ^ 32 := by omega
      have hj' := hjW64
      generalize sint.nat j = b at h1 h2 hj' ⊢
      rw [hj']
      generalize dataOff ms b = a at h1 h2 ⊢
      rw [show (((a - (16 + 16 * b) : Nat)) : Int) = (a : Int) - 16 - 16 * (b : Int) by omega]
      word
    have hoffW : W64 (dataOff ms (sint.nat j) : Int) + W64 ((m.key ++ m.value).length : Int) =
        W64 (dataOff ms (sint.nat j + 1) : Int) := by
      rw [hsucc, show m.kv = m.key ++ m.value from rfl]; push_cast; word
    rw [hposW, hoffW]
    have hjW : uint.Z (W16 (sint.Z j)) = sint.nat j := by
      rw [hjZ]; simp only [uint.Z]; word
    have hElen : ∀ lf, (elemsPrefix lf ms (sint.nat j) ++
        (rest.drop (16 * sint.nat j)).take (16 * (ms.length - sint.nat j))).length =
          16 * ms.length := by
      intro lf
      rw [List.length_append, elemsPrefix_length _ _ _ (by omega)]
      simp only [List.length_take, List.length_drop]; omega
    cases hL : leaf
    -- a branch element
    wp_auto
    wp_apply wp_Page_BranchPageElement
    · ipureintro; exact Hp0
    · ipureintro; rw [hjW]; omega
    rw [hjW]
    icases bytesPointsto_view_at (V := branchPageElement) (p +ₗ 16) _ _ (16 * sint.nat j)
      (p +ₗ (16 + 16 * (sint.nat j : Int))) (by rw [loc_add_assoc]; congr 1; try omega)
      (by rw [hElen]; omega) (by simp [Loc.add]; omega) $$ HE
      with ⟨Hel, HE⟩
    wp_apply wp_branchPageElement_SetPos $$ [$Hel] as Hel
    wp_apply wp_Inode_Key $$ [$item] as item
    wp_apply wp_branchPageElement_SetKsize $$ [$Hel] as Hel
    wp_apply wp_Inode_Pgid $$ [$item] as item
    wp_apply wp_branchPageElement_SetPgid $$ [$Hel] as Hel
    wp_apply wp_branchPageElement_Pgid $$ [$Hel] as Hel
    wp_apply wp_Page_Id $$ [$Hp] as Hp
    rw [decide_eq_false (show ¬ x.pgid' = hdr.id' by rw [Hxfp.2]; exact hcircj hL)]
    wp_apply wp_Assert
    have hlt : sint.nat j < (branchElems ms).length := by rw [branchElems_length]; exact hjn
    ispecialize HE $$ %((branchElems ms)[sint.nat j]'hlt)
    ihave HE := HE $$ [Hel]
    · iapply typedPointsto_of_eq
      iframe Hel
      ipureintro
      rw [branchElems_getElem]
      simp only [hmj, branchPageElement.mk.injEq]
      refine ⟨trivial, ?_, Hxfp.2⟩
      rw [hkW, hkZ]
    rw [elemsRegion_step_branch ms rest (sint.nat j) hjn]
    rotate_left
    wp_auto
    wp_apply wp_Page_LeafPageElement
    · ipureintro; exact Hp0
    · ipureintro; rw [hjW]; omega
    rw [hjW]
    icases bytesPointsto_view_at (V := leafPageElement) (p +ₗ 16) _ _ (16 * sint.nat j)
      (p +ₗ (16 + 16 * (sint.nat j : Int))) (by rw [loc_add_assoc]; congr 1; try omega)
      (by rw [hElen]; omega) (by simp [Loc.add]; omega) $$ HE
      with ⟨Hel, HE⟩
    wp_apply wp_leafPageElement_SetPos $$ [$Hel] as Hel
    wp_apply wp_Inode_Flags $$ [$item] as item
    wp_apply wp_leafPageElement_SetFlags $$ [$Hel] as Hel
    wp_apply wp_Inode_Key $$ [$item] as item
    wp_apply wp_leafPageElement_SetKsize $$ [$Hel] as Hel
    wp_apply wp_Inode_Value $$ [$item] as item
    wp_apply wp_leafPageElement_SetVsize $$ [$Hel] as Hel
    have hlt : sint.nat j < (leafElems ms).length := by rw [leafElems_length]; exact hjn
    ispecialize HE $$ %((leafElems ms)[sint.nat j]'hlt)
    ihave HE := HE $$ [Hel]
    · iapply typedPointsto_of_eq
      iframe Hel
      ipureintro
      rw [leafElems_getElem]
      simp only [hmj, leafPageElement.mk.injEq]
      refine ⟨Hxfp.1, trivial, ?_, ?_⟩
      · rw [hkW, hkZ]
      · rw [hvW, sint_Z_W64_nat _ (by simp at hDle; omega)]
    rw [elemsRegion_step_leaf ms rest (sint.nat j) hjn]
    all_goals
      -- the data area: the inode's key and value replace the bytes at `dataOff`
      have hR : dataOff ms (sint.nat j) + (m.key ++ m.value).length ≤ 16 + rest.length := by
        omega
      icases (bytesPointsto_app _ _ _ _).1 $$ HD with ⟨HD1, HD2⟩
      icases bytesPointsto_congr _ _ _
        ((((rest.drop (16 * ms.length)).drop (dataBytes (ms.take (sint.nat j))).length).take
            (m.key ++ m.value).length) ++
          (((rest.drop (16 * ms.length)).drop (dataBytes (ms.take (sint.nat j))).length).drop
            (m.key ++ m.value).length)) (List.take_append_drop _ _).symm $$ HD2 with HD2
      icases (bytesPointsto_app _ _ _ _).1 $$ HD2 with ⟨Hc, HD3⟩
      have haddr : p +ₗ (16 + ((16 * ms.length : Nat) : Int)) +ₗ
          ((dataBytes (ms.take (sint.nat j))).length : Int) = p +ₗ (dataOff ms (sint.nat j) : Int) := by
        rw [loc_add_assoc]; congr 1; try omega
      have hClen : (((rest.drop (16 * ms.length)).drop
          (dataBytes (ms.take (sint.nat j))).length).take (m.key ++ m.value).length).length =
            (m.key ++ m.value).length := by
        simp only [List.length_take, List.length_drop]; omega
      generalize (((rest.drop (16 * ms.length)).drop
          (dataBytes (ms.take (sint.nat j))).length).take (m.key ++ m.value).length) = C at hClen
      rw [haddr]
      icases (bytesPointsto_ownSlice _ _ _ (by simp only [Loc.add]; omega) (by omega)).1 $$ Hc
        with Hc
      rw [hClen]
      wp_apply wp_Inode_Key $$ [$item] as item
      wp_apply wp_slice_copy _ C x.key' m.key (qk (sint.nat j)) $$ [Hc Hkey] as %n ⟨%Hn, Hc, Hkey⟩
      · iframe
      have hkl : m.key.length ≤ C.length := by rw [hClen]; simp
      rw [List.take_of_length_le hkl] at *
      have hnW : n = W64 (m.key.length : Int) := by
        have h1 : sint.nat n = m.key.length := by rw [Hn]; omega
        have h2 : 0 ≤ sint.Z n := by
          have : (sint.Z n).toNat = m.key.length := h1
          omega
        exact w64_of_sint_nat _ _ h1.symm h2
      subst hnW
      have hklZ : sint.Z (W64 (m.key.length : Int)) = m.key.length := hkZ
      rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by rw [hklZ]; omega,
        by rw [hklZ, hszZ]; simp only [List.length_append]; omega, Int.le_refl _⟩)]
      wp_auto
      wp_apply wp_Inode_Value $$ [$item] as item
      have hsplit : 0 ≤ sint.Z (W64 (m.key.length : Int)) ∧ sint.Z (W64 (m.key.length : Int)) ≤
          sint.Z (slice.mk (p +ₗ (dataOff ms (sint.nat j) : Int)) (W64 ((m.key ++ m.value).length : Int))
            (W64 ((m.key ++ m.value).length : Int))).len := by
        constructor
        · rw [hklZ]; omega
        · change sint.Z (W64 (m.key.length : Int)) ≤ sint.Z (W64 ((m.key ++ m.value).length : Int))
          rw [hklZ, hszZ]; simp only [List.length_append]; omega
      icases (ownSlice_split_all (W64 (m.key.length : Int)) _ _ _ hsplit).1 $$ Hc with ⟨Hc1, Hc2⟩
      have hkn : sint.nat (W64 (m.key.length : Int)) = m.key.length := by
        simp only [sint.nat, hklZ]; omega
      rw [hkn, List.take_left' rfl, List.drop_left' rfl,
        show (slice.mk (p +ₗ (dataOff ms (sint.nat j) : Int)) (W64 ((m.key ++ m.value).length : Int))
          (W64 ((m.key ++ m.value).length : Int))).len = W64 ((m.key ++ m.value).length : Int) from rfl]
      wp_apply wp_slice_copy _ _ x.value' m.value (qv (sint.nat j)) $$ [Hc2 Hval] as %n2 ⟨-, Hc2, Hval⟩
      · iframe
      have hvl : (C.drop m.key.length).length = m.value.length := by
        simp only [List.length_drop, hClen, List.length_append]; omega
      rw [List.drop_eq_nil_of_le (Nat.le_of_eq hvl), hvl, List.take_of_length_le (Nat.le_refl _),
        List.append_nil]
      icases (ownSlice_split_all (V := w8) (W64 (m.key.length : Int)) _ _ (m.key ++ m.value)
        hsplit).2 $$ [Hc1 Hc2] with Hc
      · rw [hkn, List.take_left' rfl, List.drop_left' rfl,
          show (slice.mk (p +ₗ (dataOff ms (sint.nat j) : Int)) (W64 ((m.key ++ m.value).length : Int))
            (W64 ((m.key ++ m.value).length : Int))).len = W64 ((m.key ++ m.value).length : Int) from rfl]
        iframe
      icases (bytesPointsto_ownSlice (p +ₗ (dataOff ms (sint.nat j) : Int)) _ (m.key ++ m.value)
        (by simp only [Loc.add]; omega) (by omega)).2 $$ Hc with Hc
      ihave HD : bytesPointsto (p +ₗ ((16 : Int) + ((16 * ms.length : Nat) : Int))) (DFrac.own 1)
          (dataBytes (ms.take (sint.nat j + 1)) ++ (rest.drop (16 * ms.length)).drop
            (dataBytes (ms.take (sint.nat j + 1))).length) $$ [HD1 Hc HD3]
      · rw [← hstep, List.append_assoc]
        iapply (bytesPointsto_app _ _ _ _).2
        iframe HD1
        rw [haddr]
        iapply (bytesPointsto_app _ _ _ _).2
        iframe
      ispecialize Hins $$ [Hkey Hval]
      · iframe; ipureintro; exact Hxfp
      wp_for_post
      have hj1 : sint.nat (j + W64 1) = sint.nat j + 1 := by
        show (sint.Z (j + W64 1)).toNat = (sint.Z j).toNat + 1
        have : sint.Z (j + W64 1) = sint.Z j + 1 := by word
        omega
      iexists (j + W64 1), j
      rw [hj1]
      iframe
      ipureintro
      constructor <;> word
  · rw [decide_eq_false hexit]
    simp only [Bool.false_eq_true, ↓reduceIte]
    wp_auto
    have hjn : sint.nat j = ms.length := by
      rw [hsZ] at hexit; have := Hj.2; simp only [sint.nat, sint.Z] at this hexit ⊢; omega
    rw [hjn, elemsPrefix_full, Nat.sub_self, Nat.mul_zero, List.take_zero, List.append_nil,
      List.take_length, List.drop_drop, dataOff_full]
    have hbl : (pageBody leaf ms).length = (pageBody true ms).length := by
      simp [pageBody_length]
    rw [hbl, show W32 (uint.Z (W64 ((16 + (pageBody true ms).length : Nat) : Int))) =
      W32 ((16 + (pageBody true ms).length : Nat) : Int) by
        apply BitVec.eq_of_toNat_eq; simp [uint.Z, W32, W64]; omega]
    iapply HΦ
    iframe
    rw [show pageBody leaf ms ++ List.drop (pageBody true ms).length rest =
      elemBytes leaf ms ++ (dataBytes ms ++ List.drop (16 * ms.length + (dataBytes ms).length) rest) by
        rw [pageBody_length, pageBody, List.append_assoc]]
    iapply (bytesPointsto_app _ _ _ _).2
    iframe HE
    rw [elemBytes_length, loc_add_assoc]
    iexact HD

end proof

end common
end internal
end bbolt
end EtcdGrove
end Perennial
