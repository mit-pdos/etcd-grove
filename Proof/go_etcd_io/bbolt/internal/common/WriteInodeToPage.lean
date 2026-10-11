module
public import Spec.go_etcd_io.bbolt.internal.common.WriteInodeToPage
public import Proof.go_etcd_io.bbolt.internal.common.Inodes
public import Spec.go_etcd_io.bbolt.internal.common.Page__PageElementSize
public import Spec.go_etcd_io.bbolt.internal.common.Page__IsLeafPage
public import Spec.go_etcd_io.bbolt.internal.common.Page__LeafPageElement
public import Spec.go_etcd_io.bbolt.internal.common.Page__BranchPageElement
public import Spec.go_etcd_io.bbolt.internal.common.Page__Id
public import Spec.go_etcd_io.bbolt.internal.common.leafPageElement__SetPos
public import Spec.go_etcd_io.bbolt.internal.common.leafPageElement__SetFlags
public import Spec.go_etcd_io.bbolt.internal.common.leafPageElement__SetKsize
public import Spec.go_etcd_io.bbolt.internal.common.leafPageElement__SetVsize
public import Spec.go_etcd_io.bbolt.internal.common.branchPageElement__SetPos
public import Spec.go_etcd_io.bbolt.internal.common.branchPageElement__SetKsize
public import Spec.go_etcd_io.bbolt.internal.common.branchPageElement__SetPgid
public import Spec.go_etcd_io.bbolt.internal.common.branchPageElement__Pgid
public import Spec.go_etcd_io.bbolt.internal.common.Inode__Key
public import Spec.go_etcd_io.bbolt.internal.common.Inode__Value
public import Spec.go_etcd_io.bbolt.internal.common.Inode__Flags
public import Spec.go_etcd_io.bbolt.internal.common.Inode__Pgid
public import Spec.go_etcd_io.bbolt.internal.common.UnsafeByteSlice
public import Spec.go_etcd_io.bbolt.internal.common.Assert

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt.internal.common

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.internal.common.Assumptions]

-- Two loop bodies (leaf, branch) of byte-level reasoning: over the default budget.
set_option maxHeartbeats 800000 in
theorem WriteInodeToPage.wp_proof
    (hPE : Page.PageElementSize.spec (GF := GF) (hG := hG))
    (hLeaf : Page.IsLeafPage.spec (GF := GF) (hG := hG))
    (hLE : Page.LeafPageElement.spec (GF := GF) (hG := hG))
    (hBE : Page.BranchPageElement.spec (GF := GF) (hG := hG))
    (hId : Page.Id.spec (GF := GF) (hG := hG))
    (hLSP : leafPageElement.SetPos.spec (GF := GF) (hG := hG))
    (hLSF : leafPageElement.SetFlags.spec (GF := GF) (hG := hG))
    (hLSK : leafPageElement.SetKsize.spec (GF := GF) (hG := hG))
    (hLSV : leafPageElement.SetVsize.spec (GF := GF) (hG := hG))
    (hBSP : branchPageElement.SetPos.spec (GF := GF) (hG := hG))
    (hBSK : branchPageElement.SetKsize.spec (GF := GF) (hG := hG))
    (hBSG : branchPageElement.SetPgid.spec (GF := GF) (hG := hG))
    (hBG : branchPageElement.Pgid.spec (GF := GF) (hG := hG))
    (hK : Inode.Key.spec (GF := GF) (hG := hG))
    (hV : Inode.Value.spec (GF := GF) (hG := hG))
    (hF : Inode.Flags.spec (GF := GF) (hG := hG))
    (hP : Inode.Pgid.spec (GF := GF) (hG := hG))
    (hUBS : UnsafeByteSlice.spec (GF := GF) (hG := hG))
    (hA : Assert.spec (GF := GF) (hG := hG)) :
    WriteInodeToPage.spec (GF := GF) (hG := hG) := by
  intro s ins dq ks vs q p hdr rest Hc Hn Hks Hvs Hk0 Htot Hroom Hpgid
  wp_start as ⟨Hs, Hd, Hp, Hr⟩
  ihave %Hsl := ownSlice_len _ _ _ $$ Hs
  wp_auto
  wp_apply hPE $$ [$Hp] as Hp
  try wp_auto
  wp_apply hLeaf $$ [$Hp] as Hp
  try wp_auto
  have Hnl : ins.length = sint.nat s.len := Hsl.1
  have HE : 16 * ins.length ≤ rest.length := by have := Nat.zero_le (kvLen ks vs ins.length); omega
  icases (bytesPointsto_take_drop (p +ₗ 16) _ rest (16 * ins.length) HE).1 $$ Hr with ⟨HE2, HD2⟩
  ihave HE1 := (bytesPointsto_nil (p +ₗ 16) (DFrac.own 1)).2 $$ []
  · iempintro
  ihave HD1 := (bytesPointsto_nil (p +ₗ (16 + 16 * (ins.length : Int))) (DFrac.own 1)).2 $$ []
  · iempintro
  rename_i iu_ptr
  irename: (iu_ptr ↦ (_ : w64)) => iu
  ihave IH : (∃ (c : w64) (iv : w64),
      "i" ∷ i_ptr ↦ c ∗ "iu" ∷ iu_ptr ↦ iv ∗
      "off" ∷ off_ptr ↦ W64 (dataOff ins.length ks vs (sint.nat c) : Int) ∗
      "Hs" ∷ s ↦*{dq} ins ∗ "Hd" ∷ inodeData ins ks vs q ∗ "Hp" ∷ p ↦ hdr ∗
      "isLeaf" ∷ isLeaf_ptr ↦ decide (hdr.flags' = W16 2) ∗ "p" ∷ p_ptr ↦ p ∗
      "HE1" ∷ bytesPointsto (p +ₗ 16) (DFrac.own 1)
        (writtenUpTo (decide (hdr.flags' = W16 2)) ks vs ins (sint.nat c)) ∗
      "HE2" ∷ bytesPointsto (p +ₗ (16 + 16 * (sint.nat c : Int))) (DFrac.own 1)
        ((rest.take (16 * ins.length)).drop (16 * sint.nat c)) ∗
      "HD1" ∷ bytesPointsto (p +ₗ (16 + 16 * (ins.length : Int))) (DFrac.own 1)
        (kvUpTo ks vs (sint.nat c)) ∗
      "HD2" ∷ bytesPointsto (p +ₗ (dataOff ins.length ks vs (sint.nat c) : Int)) (DFrac.own 1)
        (rest.drop (16 * ins.length + kvLen ks vs (sint.nat c))) ∗
      "%Hcb" ∷ ⌜0 ≤ sint.Z c ∧ sint.Z c ≤ sint.Z s.len⌝ : IProp GF)
    $$ [i iu off Hs Hd Hp isLeaf p HE1 HE2 HD1 HD2]
  · iexists W64 0, zero_val w64
    simp only [named]
    rw [show sint.nat (W64 0) = 0 from rfl, writtenUpTo_zero, kvUpTo_zero, kvLen_zero,
      Nat.mul_zero, List.drop_zero, Nat.add_zero]
    unfold dataOff
    rw [kvLen_zero, Nat.add_zero]
    simp only [loc_add_assoc]
    iframe
    isplitl [off]
    · iExactEq off; congr 1
      have := Hsl.2; rw [Hnl]; push_cast; word
    · ipureintro; constructor <;> word
  wp_for IH
  wp_if_destruct
  · have Hlt : sint.Z c < sint.Z s.len := Hif
    have Hj : sint.nat c < ins.length := by rw [Hnl]; word
    obtain ⟨it, Hit⟩ : ∃ it, ins[sint.nat c]? = some it :=
      ⟨_, List.getElem?_eq_getElem Hj⟩
    rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨Hcb.1, Hlt⟩)]
    wp_apply wp_load_slice_index s (sint.Z c) ins dq it Hcb.1 $$ [Hs] as Hs
    · iframe; ipureintro; exact Hit
    try wp_auto
    unfold inodeData
    icases BigSepL.bigSepL_lookup_acc Hit $$ Hd with ⟨⟨Hk, Hv⟩, Hdb⟩
    ihave %Hkl := ownSlice_len _ _ _ $$ Hk
    ihave %Hvl := ownSlice_len _ _ _ $$ Hv
    have Hk0j := Hk0 _ Hj
    wp_apply hK $$ [$item] as item
    try wp_auto
    rw [decide_eq_true (show sint.Z (W64 0) < sint.Z it.key'.len by
      have := Hkl.1; have := Hkl.2; word)]
    wp_apply hA
    try wp_auto
    wp_apply hK $$ [$item] as item
    try wp_auto
    wp_apply hV $$ [$item] as item
    try wp_auto
    have Hks1 : sint.nat c < ks.length := by omega
    have Hvs1 : sint.nat c < vs.length := by omega
    have HkvS := kvLen_succ ks vs (sint.nat c) Hks1 Hvs1
    have HkvM := kvLen_mono ks vs (sint.nat c + 1) ins.length (by omega)
    have HszZ : sint.Z (it.key'.len + it.value'.len) =
        ((ks.getD (sint.nat c) []).length + (vs.getD (sint.nat c) []).length : Nat) := by
      have := Hkl.1; have := Hkl.2; have := Hvl.1; have := Hvl.2; push_cast; word
    have Hdj : (dataOff ins.length ks vs (sint.nat c) : Int) < 2 ^ 63 := by unfold dataOff; omega
    wp_apply hUBS p (W64 (dataOff ins.length ks vs (sint.nat c) : Int)) (W64 0)
      (it.key'.len + it.value'.len) Hc (by decide) (by rw [HszZ]; word) (by rw [HszZ]; omega)
    try wp_auto
    have Hb0 : sint.Z (W64 (dataOff ins.length ks vs (sint.nat c) : Int)) + sint.Z (W64 0) =
        (dataOff ins.length ks vs (sint.nat c) : Int) := by word
    have Hsz0 : it.key'.len + it.value'.len - W64 0 = it.key'.len + it.value'.len := by
      simp
    have HdS : dataOff ins.length ks vs (sint.nat c + 1) = dataOff ins.length ks vs (sint.nat c) +
        ((ks.getD (sint.nat c) []).length + (vs.getD (sint.nat c) []).length) := by
      unfold dataOff; rw [HkvS]; omega
    have Hoff : W64 (dataOff ins.length ks vs (sint.nat c) : Int) + (it.key'.len + it.value'.len) =
        W64 (dataOff ins.length ks vs (sint.nat c + 1) : Int) := by
      rw [HdS]; have := HszZ; word
    rw [Hb0, Hsz0, Hoff]
    have Hit' : ins.getD (sint.nat c) (zero_val Inode) = it := by
      rw [List.getD_eq_getElem?_getD, Hit]; rfl
    have HE2l : 16 ≤ ((rest.take (16 * ins.length)).drop (16 * sint.nat c)).length := by
      simp; omega
    icases (bytesPointsto_take_drop _ _ _ 16 HE2l).1 $$ HE2 with ⟨Hel, HE2⟩
    have Hcar : (p +ₗ (16 + 16 * (sint.nat c : Int))).locCar ≠ 0 := by simpa [Loc.add] using Hc
    by_cases HL : hdr.flags' = W16 2
    · rw [decide_eq_true HL]
      try wp_auto
      have He0 : (List.take 16 (List.drop (16 * sint.nat c) (List.take (16 * ins.length) rest))).length
          = 16 := by rw [List.length_take]; omega
      rw [← leafElemBytes_any _ He0]
      icases (leafElem_bytes (hG := hG) _ _ _ Hcar).2 $$ Hel with Hel
      wp_apply hLE
      rw [show (16 : Int) + 16 * uint.Z (W16 (sint.Z c)) = 16 + 16 * (sint.nat c : Int) by word]
      try wp_auto
      rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by decide, by rw [HszZ, show sint.Z (W64 0) = 0 from rfl]; push_cast; omega⟩)]
      unfold sliceIndexRef
      rw [show sint.Z (W64 0) = 0 from rfl, arrayIndexRef_zero]
      try wp_auto
      wp_apply hLSP $$ [$Hel] as Hel
      try wp_auto
      wp_apply hF $$ [$item] as item
      wp_apply hLSF $$ [$Hel] as Hel
      try wp_auto
      wp_apply hK $$ [$item] as item
      try wp_auto
      wp_apply hLSK $$ [$Hel] as Hel
      try wp_auto
      wp_apply hV $$ [$item] as item
      try wp_auto
      wp_apply hLSV $$ [$Hel] as Hel
      try wp_auto
      -- the key and the value into `b`
      have HD2l : (ks.getD (sint.nat c) []).length + (vs.getD (sint.nat c) []).length ≤
          (rest.drop (16 * ins.length + kvLen ks vs (sint.nat c))).length := by
        simp only [List.length_drop]; omega
      icases (bytesPointsto_take_drop _ _ _ _ HD2l).1 $$ HD2 with ⟨Hb, HD2⟩
      have HbLen : ((rest.drop (16 * ins.length + kvLen ks vs (sint.nat c))).take
          ((ks.getD (sint.nat c) []).length + (vs.getD (sint.nat c) []).length)).length =
          (ks.getD (sint.nat c) []).length + (vs.getD (sint.nat c) []).length := by
        rw [List.length_take]; omega
      ihave Hbs := (ownSlice_bytes (slice.mk (p +ₗ (dataOff ins.length ks vs (sint.nat c) : Int))
          (it.key'.len + it.value'.len) (it.key'.len + it.value'.len)) _ (DFrac.own 1)
          (List.ne_nil_of_length_pos (by rw [HbLen]; omega))).2 $$ [Hb]
      · iframe; ipureintro; simp only; rw [HbLen, HszZ]; constructor <;> push_cast <;> omega
      wp_apply hK $$ [$item] as item
      wp_apply wp_slice_copy (V := w8) _ _ it.key' (ks.getD (sint.nat c) []) q $$ [Hbs Hk]
        as %n1 ⟨%Hn1, Hbs, Hk⟩
      · iframe
      have HtK : (ks.getD (sint.nat c) []).take ((rest.drop (16 * ins.length + kvLen ks vs (sint.nat c))).take
          ((ks.getD (sint.nat c) []).length + (vs.getD (sint.nat c) []).length)).length =
          ks.getD (sint.nat c) [] := List.take_of_length_le (by rw [HbLen]; omega)
      have Hn1n : sint.nat n1 = (ks.getD (sint.nat c) []).length := by rw [Hn1, HbLen]; omega
      have Hn1Z : sint.Z n1 = ((ks.getD (sint.nat c) []).length : Int) := by
        have := Hk0j; have h : sint.nat n1 = (sint.Z n1).toNat := rfl; omega
      rw [HtK]
      try wp_auto
      rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by rw [Hn1Z]; omega,
        by rw [Hn1Z, HszZ]; omega, Int.le_refl _⟩)]
      try wp_auto
      icases (ownSlice_split_all (V := w8) n1 (slice.mk (p +ₗ (dataOff ins.length ks vs (sint.nat c) : Int))
          (it.key'.len + it.value'.len) (it.key'.len + it.value'.len)) (DFrac.own 1) _
          ⟨by rw [Hn1Z]; omega, by simp only; rw [Hn1Z, HszZ]; omega⟩).1 $$ Hbs with ⟨Hb1, Hb2⟩
      rw [Hn1n, List.take_left, List.drop_left]
      wp_apply hV $$ [$item] as item
      wp_apply wp_slice_copy (V := w8) _ _ it.value' (vs.getD (sint.nat c) []) q $$ [Hb2 Hv]
        as %n2 ⟨-, Hb2, Hv⟩
      · isplitl [Hb2]
        · iexact Hb2
        · iexact Hv
      have Hdl : (((rest.drop (16 * ins.length + kvLen ks vs (sint.nat c))).take
          ((ks.getD (sint.nat c) []).length + (vs.getD (sint.nat c) []).length)).drop
          (ks.getD (sint.nat c) []).length).length = (vs.getD (sint.nat c) []).length := by
        rw [List.length_drop, HbLen]; omega
      rw [Hdl, List.take_length, List.drop_eq_nil_of_le (Nat.le_of_eq Hdl), List.append_nil]
      ihave Hbs : (slice.mk (p +ₗ (dataOff ins.length ks vs (sint.nat c) : Int))
          (it.key'.len + it.value'.len) (it.key'.len + it.value'.len) ↦*
          (ks.getD (sint.nat c) [] ++ vs.getD (sint.nat c) []) : IProp GF) $$ [Hb1 Hb2]
      · iapply (ownSlice_split_all (V := w8) n1 (slice.mk (p +ₗ (dataOff ins.length ks vs (sint.nat c) : Int))
          (it.key'.len + it.value'.len) (it.key'.len + it.value'.len)) (DFrac.own 1) _
          ⟨by rw [Hn1Z]; omega, by simp only; rw [Hn1Z, HszZ]; omega⟩).2
        rw [Hn1n, List.take_left, List.drop_left]
        isplitl [Hb1]
        · iexact Hb1
        · iexact Hb2
      icases (ownSlice_bytes _ _ (DFrac.own 1) (List.ne_nil_of_length_pos
        (by rw [List.length_append]; omega))).1 $$ Hbs with ⟨Hkv, -⟩
      try wp_auto
      -- re-establish the invariant
      ispecialize Hdb $$ %it
      ihave Hd := Hdb $$ [Hk Hv]
      · iframe
      have Hset : ins.set (sint.nat c) it = ins := by
        obtain ⟨h, e⟩ := List.getElem?_eq_some_iff.1 Hit
        rw [← e, List.set_getElem_self]
      rw [Hset]
      have HposE : W32 (uint.Z (ptrAddr (p +ₗ (dataOff ins.length ks vs (sint.nat c) : Int)) -
          ptrAddr (p +ₗ (16 + 16 * (sint.nat c : Int))))) =
          W32 ((dataOff ins.length ks vs (sint.nat c) : Int) - (elemOff (sint.nat c) : Int)) := by
        rw [go.ptrAddr_add _ _ Hc, go.ptrAddr_add _ _ Hc]
        have Hge : 16 + 16 * (sint.nat c : Int) ≤ (dataOff ins.length ks vs (sint.nat c) : Int) := by
          unfold dataOff; push_cast; omega
        have h2 : ptrAddr p + BitVec.ofInt 64 (dataOff ins.length ks vs (sint.nat c) : Int) -
            (ptrAddr p + BitVec.ofInt 64 (16 + 16 * (sint.nat c : Int))) =
            BitVec.ofInt 64 (dataOff ins.length ks vs (sint.nat c) : Int) -
              BitVec.ofInt 64 (16 + 16 * (sint.nat c : Int)) := by
          bv_omega
        rw [h2]
        unfold elemOff
        push_cast
        have : (16 + 16 * (sint.nat c : Int)) < 2 ^ 63 := by omega
        word
      ihave HelB : bytesPointsto (p +ₗ 16 +ₗ ((writtenUpTo true ks vs ins (sint.nat c)).length : Int))
          (DFrac.own 1) (writtenElem true ins.length ks vs (ins.getD (sint.nat c) (zero_val Inode))
            (sint.nat c)) $$ [Hel]
      · rw [writtenUpTo_length, loc_add_assoc, Hit',
          show (16 : Int) + ((16 * sint.nat c : Nat) : Int) = 16 + 16 * (sint.nat c : Int) by push_cast; rfl]
        unfold writtenElem
        simp only [↓reduceIte]
        iapply (leafElem_bytes (hG := hG) _ _ _ Hcar).1
        iExactEq Hel
        congr 1
        simp only [leafPageElement.mk.injEq]
        refine ⟨trivial, HposE, ?_, ?_⟩
        · congr 1; rw [Hkl.1]; exact (Int.toNat_of_nonneg Hkl.2).symm
        · congr 1; rw [Hvl.1]; exact (Int.toNat_of_nonneg Hvl.2).symm
      ihave HE1 := (bytesPointsto_app (p +ₗ 16) (DFrac.own 1) (writtenUpTo true ks vs ins (sint.nat c))
          (writtenElem true ins.length ks vs (ins.getD (sint.nat c) (zero_val Inode))
            (sint.nat c))).2 $$ [HE1 HelB]
      · iframe
      rw [← writtenUpTo_succ]
      ihave Hkv : bytesPointsto (p +ₗ (16 + 16 * (ins.length : Int)) +ₗ
          ((kvUpTo ks vs (sint.nat c)).length : Int)) (DFrac.own 1)
          (ks.getD (sint.nat c) [] ++ vs.getD (sint.nat c) []) $$ [Hkv]
      · rw [kvUpTo_length _ _ _ (by omega) (by omega), loc_add_assoc]
        iExactEq Hkv
        congr 1
      ihave HD1 := (bytesPointsto_app (p +ₗ (16 + 16 * (ins.length : Int))) (DFrac.own 1)
          (kvUpTo ks vs (sint.nat c)) (ks.getD (sint.nat c) [] ++ vs.getD (sint.nat c) [])).2 $$ [HD1 Hkv]
      · iframe
      rw [← kvUpTo_succ _ _ _ Hks1 Hvs1]
      ihave HD2 : bytesPointsto (p +ₗ (dataOff ins.length ks vs (sint.nat c + 1) : Int)) (DFrac.own 1)
          (rest.drop (16 * ins.length + kvLen ks vs (sint.nat c + 1))) $$ [HD2]
      · iExactEq HD2
        congr 1
        · rw [loc_add_assoc, HdS]; congr 1 <;> (try push_cast) <;> omega
        · rw [List.drop_drop, HkvS]; congr 1; omega
      ihave HE2 : bytesPointsto (p +ₗ (16 + 16 * ((sint.nat c + 1 : Nat) : Int))) (DFrac.own 1)
          ((rest.take (16 * ins.length)).drop (16 * (sint.nat c + 1))) $$ [HE2]
      · iExactEq HE2
        congr 1
        all_goals (try rw [loc_add_assoc]); all_goals (try rw [List.drop_drop])
        all_goals (congr 1 <;> (try push_cast) <;> omega)
      wp_for_post
      iframe
      iexists c + W64 1, c
      rw [show sint.nat (c + W64 1) = sint.nat c + 1 by word]
      iframe
      ipureintro; constructor <;> word
    · rw [decide_eq_false HL]
      try wp_auto
      have He0 : (List.take 16 (List.drop (16 * sint.nat c) (List.take (16 * ins.length) rest))).length
          = 16 := by rw [List.length_take]; omega
      rw [← branchElemBytes_any _ He0]
      icases (branchElem_bytes (hG := hG) _ _ _ Hcar).2 $$ Hel with Hel
      wp_apply hBE
      rw [show (16 : Int) + 16 * uint.Z (W16 (sint.Z c)) = 16 + 16 * (sint.nat c : Int) by word]
      try wp_auto
      rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by decide, by rw [HszZ, show sint.Z (W64 0) = 0 from rfl]; push_cast; omega⟩)]
      unfold sliceIndexRef
      rw [show sint.Z (W64 0) = 0 from rfl, arrayIndexRef_zero]
      try wp_auto
      wp_apply hBSP $$ [$Hel] as Hel
      try wp_auto
      wp_apply hK $$ [$item] as item
      try wp_auto
      wp_apply hBSK $$ [$Hel] as Hel
      try wp_auto
      wp_apply hP $$ [$item] as item
      wp_apply hBSG $$ [$Hel] as Hel
      try wp_auto
      wp_apply hBG $$ [$Hel] as Hel
      wp_apply hId $$ [$Hp] as Hp
      try wp_auto
      have Hpg := Hpgid HL _ Hj
      rw [Hit'] at Hpg
      rw [decide_eq_false Hpg, Bool.not_false]
      wp_apply hA
      try wp_auto
      -- the key and the value into `b`
      have HD2l : (ks.getD (sint.nat c) []).length + (vs.getD (sint.nat c) []).length ≤
          (rest.drop (16 * ins.length + kvLen ks vs (sint.nat c))).length := by
        simp only [List.length_drop]; omega
      icases (bytesPointsto_take_drop _ _ _ _ HD2l).1 $$ HD2 with ⟨Hb, HD2⟩
      have HbLen : ((rest.drop (16 * ins.length + kvLen ks vs (sint.nat c))).take
          ((ks.getD (sint.nat c) []).length + (vs.getD (sint.nat c) []).length)).length =
          (ks.getD (sint.nat c) []).length + (vs.getD (sint.nat c) []).length := by
        rw [List.length_take]; omega
      ihave Hbs := (ownSlice_bytes (slice.mk (p +ₗ (dataOff ins.length ks vs (sint.nat c) : Int))
          (it.key'.len + it.value'.len) (it.key'.len + it.value'.len)) _ (DFrac.own 1)
          (List.ne_nil_of_length_pos (by rw [HbLen]; omega))).2 $$ [Hb]
      · iframe; ipureintro; simp only; rw [HbLen, HszZ]; constructor <;> push_cast <;> omega
      wp_apply hK $$ [$item] as item
      wp_apply wp_slice_copy (V := w8) _ _ it.key' (ks.getD (sint.nat c) []) q $$ [Hbs Hk]
        as %n1 ⟨%Hn1, Hbs, Hk⟩
      · iframe
      have HtK : (ks.getD (sint.nat c) []).take ((rest.drop (16 * ins.length + kvLen ks vs (sint.nat c))).take
          ((ks.getD (sint.nat c) []).length + (vs.getD (sint.nat c) []).length)).length =
          ks.getD (sint.nat c) [] := List.take_of_length_le (by rw [HbLen]; omega)
      have Hn1n : sint.nat n1 = (ks.getD (sint.nat c) []).length := by rw [Hn1, HbLen]; omega
      have Hn1Z : sint.Z n1 = ((ks.getD (sint.nat c) []).length : Int) := by
        have := Hk0j; have h : sint.nat n1 = (sint.Z n1).toNat := rfl; omega
      rw [HtK]
      try wp_auto
      rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by rw [Hn1Z]; omega,
        by rw [Hn1Z, HszZ]; omega, Int.le_refl _⟩)]
      try wp_auto
      icases (ownSlice_split_all (V := w8) n1 (slice.mk (p +ₗ (dataOff ins.length ks vs (sint.nat c) : Int))
          (it.key'.len + it.value'.len) (it.key'.len + it.value'.len)) (DFrac.own 1) _
          ⟨by rw [Hn1Z]; omega, by simp only; rw [Hn1Z, HszZ]; omega⟩).1 $$ Hbs with ⟨Hb1, Hb2⟩
      rw [Hn1n, List.take_left, List.drop_left]
      wp_apply hV $$ [$item] as item
      wp_apply wp_slice_copy (V := w8) _ _ it.value' (vs.getD (sint.nat c) []) q $$ [Hb2 Hv]
        as %n2 ⟨-, Hb2, Hv⟩
      · isplitl [Hb2]
        · iexact Hb2
        · iexact Hv
      have Hdl : (((rest.drop (16 * ins.length + kvLen ks vs (sint.nat c))).take
          ((ks.getD (sint.nat c) []).length + (vs.getD (sint.nat c) []).length)).drop
          (ks.getD (sint.nat c) []).length).length = (vs.getD (sint.nat c) []).length := by
        rw [List.length_drop, HbLen]; omega
      rw [Hdl, List.take_length, List.drop_eq_nil_of_le (Nat.le_of_eq Hdl), List.append_nil]
      ihave Hbs : (slice.mk (p +ₗ (dataOff ins.length ks vs (sint.nat c) : Int))
          (it.key'.len + it.value'.len) (it.key'.len + it.value'.len) ↦*
          (ks.getD (sint.nat c) [] ++ vs.getD (sint.nat c) []) : IProp GF) $$ [Hb1 Hb2]
      · iapply (ownSlice_split_all (V := w8) n1 (slice.mk (p +ₗ (dataOff ins.length ks vs (sint.nat c) : Int))
          (it.key'.len + it.value'.len) (it.key'.len + it.value'.len)) (DFrac.own 1) _
          ⟨by rw [Hn1Z]; omega, by simp only; rw [Hn1Z, HszZ]; omega⟩).2
        rw [Hn1n, List.take_left, List.drop_left]
        isplitl [Hb1]
        · iexact Hb1
        · iexact Hb2
      icases (ownSlice_bytes _ _ (DFrac.own 1) (List.ne_nil_of_length_pos
        (by rw [List.length_append]; omega))).1 $$ Hbs with ⟨Hkv, -⟩
      try wp_auto
      -- re-establish the invariant
      ispecialize Hdb $$ %it
      ihave Hd := Hdb $$ [Hk Hv]
      · iframe
      have Hset : ins.set (sint.nat c) it = ins := by
        obtain ⟨h, e⟩ := List.getElem?_eq_some_iff.1 Hit
        rw [← e, List.set_getElem_self]
      rw [Hset]
      have HposE : W32 (uint.Z (ptrAddr (p +ₗ (dataOff ins.length ks vs (sint.nat c) : Int)) -
          ptrAddr (p +ₗ (16 + 16 * (sint.nat c : Int))))) =
          W32 ((dataOff ins.length ks vs (sint.nat c) : Int) - (elemOff (sint.nat c) : Int)) := by
        rw [go.ptrAddr_add _ _ Hc, go.ptrAddr_add _ _ Hc]
        have Hge : 16 + 16 * (sint.nat c : Int) ≤ (dataOff ins.length ks vs (sint.nat c) : Int) := by
          unfold dataOff; push_cast; omega
        have h2 : ptrAddr p + BitVec.ofInt 64 (dataOff ins.length ks vs (sint.nat c) : Int) -
            (ptrAddr p + BitVec.ofInt 64 (16 + 16 * (sint.nat c : Int))) =
            BitVec.ofInt 64 (dataOff ins.length ks vs (sint.nat c) : Int) -
              BitVec.ofInt 64 (16 + 16 * (sint.nat c : Int)) := by
          bv_omega
        rw [h2]
        unfold elemOff
        push_cast
        have : (16 + 16 * (sint.nat c : Int)) < 2 ^ 63 := by omega
        word
      ihave HelB : bytesPointsto (p +ₗ 16 +ₗ ((writtenUpTo false ks vs ins (sint.nat c)).length : Int))
          (DFrac.own 1) (writtenElem false ins.length ks vs (ins.getD (sint.nat c) (zero_val Inode))
            (sint.nat c)) $$ [Hel]
      · rw [writtenUpTo_length, loc_add_assoc, Hit',
          show (16 : Int) + ((16 * sint.nat c : Nat) : Int) = 16 + 16 * (sint.nat c : Int) by push_cast; rfl]
        unfold writtenElem
        simp only [Bool.false_eq_true, ↓reduceIte]
        iapply (branchElem_bytes (hG := hG) _ _ _ Hcar).1
        iExactEq Hel
        congr 1
        simp only [branchPageElement.mk.injEq]
        refine ⟨HposE, ?_, trivial⟩
        congr 1; rw [Hkl.1]; exact (Int.toNat_of_nonneg Hkl.2).symm
      ihave HE1 := (bytesPointsto_app (p +ₗ 16) (DFrac.own 1) (writtenUpTo false ks vs ins (sint.nat c))
          (writtenElem false ins.length ks vs (ins.getD (sint.nat c) (zero_val Inode))
            (sint.nat c))).2 $$ [HE1 HelB]
      · iframe
      rw [← writtenUpTo_succ]
      ihave Hkv : bytesPointsto (p +ₗ (16 + 16 * (ins.length : Int)) +ₗ
          ((kvUpTo ks vs (sint.nat c)).length : Int)) (DFrac.own 1)
          (ks.getD (sint.nat c) [] ++ vs.getD (sint.nat c) []) $$ [Hkv]
      · rw [kvUpTo_length _ _ _ (by omega) (by omega), loc_add_assoc]
        iExactEq Hkv
        congr 1
      ihave HD1 := (bytesPointsto_app (p +ₗ (16 + 16 * (ins.length : Int))) (DFrac.own 1)
          (kvUpTo ks vs (sint.nat c)) (ks.getD (sint.nat c) [] ++ vs.getD (sint.nat c) [])).2 $$ [HD1 Hkv]
      · iframe
      rw [← kvUpTo_succ _ _ _ Hks1 Hvs1]
      ihave HD2 : bytesPointsto (p +ₗ (dataOff ins.length ks vs (sint.nat c + 1) : Int)) (DFrac.own 1)
          (rest.drop (16 * ins.length + kvLen ks vs (sint.nat c + 1))) $$ [HD2]
      · iExactEq HD2
        congr 1
        · rw [loc_add_assoc, HdS]; congr 1 <;> (try push_cast) <;> omega
        · rw [List.drop_drop, HkvS]; congr 1; omega
      ihave HE2 : bytesPointsto (p +ₗ (16 + 16 * ((sint.nat c + 1 : Nat) : Int))) (DFrac.own 1)
          ((rest.take (16 * ins.length)).drop (16 * (sint.nat c + 1))) $$ [HE2]
      · iExactEq HE2
        congr 1
        all_goals (try rw [loc_add_assoc]); all_goals (try rw [List.drop_drop])
        all_goals (congr 1 <;> (try push_cast) <;> omega)
      wp_for_post
      iframe
      iexists c + W64 1, c
      rw [show sint.nat (c + W64 1) = sint.nat c + 1 by word]
      iframe
      ipureintro; constructor <;> word
  · have Hge : sint.Z s.len ≤ sint.Z c := by word
    have Heq : sint.nat c = ins.length := by word
    try wp_auto
    rw [Heq]
    have HL1 : p +ₗ (16 + 16 * (ins.length : Int)) = p +ₗ 16 +ₗ
        ((writtenUpTo (decide (hdr.flags' = W16 2)) ks vs ins ins.length).length : Int) := by
      rw [writtenUpTo_length, loc_add_assoc]; congr 1
    have HL2 : p +ₗ (dataOff ins.length ks vs ins.length : Int) = p +ₗ 16 +ₗ
        ((writtenUpTo (decide (hdr.flags' = W16 2)) ks vs ins ins.length ++
          kvUpTo ks vs ins.length).length : Int) := by
      rw [List.length_append, writtenUpTo_length, kvUpTo_length _ _ _ (by omega) (by omega),
        loc_add_assoc]
      unfold dataOff; congr 1; push_cast; omega
    rw [HL1, HL2]
    ihave HE1 := (bytesPointsto_app (p +ₗ 16) (DFrac.own 1)
        (writtenUpTo (decide (hdr.flags' = W16 2)) ks vs ins ins.length)
        (kvUpTo ks vs ins.length)).2 $$ [HE1 HD1]
    · iframe
    ihave HE1 := (bytesPointsto_app (p +ₗ 16) (DFrac.own 1)
        (writtenUpTo (decide (hdr.flags' = W16 2)) ks vs ins ins.length ++ kvUpTo ks vs ins.length)
        (rest.drop (16 * ins.length + kvLen ks vs ins.length))).2 $$ [HE1 HD2]
    · iframe
    rw [writtenElems_eq, kvBytes_eq ks vs ins.length Hks Hvs,
      show uint.Z (W64 (dataOff ins.length ks vs ins.length : Int)) =
        ((16 + 16 * ins.length + kvLen ks vs ins.length : Nat) : Int) by unfold dataOff; word]
    iapply HΦ; iframe

end proof

end bbolt
end EtcdGrove
end Perennial
