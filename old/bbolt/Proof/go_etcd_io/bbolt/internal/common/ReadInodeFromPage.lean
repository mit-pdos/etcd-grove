module
public import Spec.go_etcd_io.bbolt.internal.common.ReadInodeFromPage
public import Proof.go_etcd_io.bbolt.internal.common.Inodes
public import Spec.go_etcd_io.bbolt.internal.common.Page__Count
public import Spec.go_etcd_io.bbolt.internal.common.Page__IsLeafPage
public import Spec.go_etcd_io.bbolt.internal.common.Page__LeafPageElement
public import Spec.go_etcd_io.bbolt.internal.common.Page__BranchPageElement
public import Spec.go_etcd_io.bbolt.internal.common.leafPageElement__Flags
public import Spec.go_etcd_io.bbolt.internal.common.leafPageElement__Key
public import Spec.go_etcd_io.bbolt.internal.common.leafPageElement__Value
public import Spec.go_etcd_io.bbolt.internal.common.branchPageElement__Pgid
public import Spec.go_etcd_io.bbolt.internal.common.branchPageElement__Key
public import Spec.go_etcd_io.bbolt.internal.common.Inode__SetFlags
public import Spec.go_etcd_io.bbolt.internal.common.Inode__SetKey
public import Spec.go_etcd_io.bbolt.internal.common.Inode__SetValue
public import Spec.go_etcd_io.bbolt.internal.common.Inode__SetPgid
public import Spec.go_etcd_io.bbolt.internal.common.Inode__Key
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

theorem ReadInodeFromPage.wp_proof
    (hCount : Page.Count.spec (GF := GF) (hG := hG))
    (hLeaf : Page.IsLeafPage.spec (GF := GF) (hG := hG))
    (hLE : Page.LeafPageElement.spec (GF := GF) (hG := hG))
    (hBE : Page.BranchPageElement.spec (GF := GF) (hG := hG))
    (hLF : leafPageElement.Flags.spec (GF := GF) (hG := hG))
    (hLK : leafPageElement.Key.spec (GF := GF) (hG := hG))
    (hLV : leafPageElement.Value.spec (GF := GF) (hG := hG))
    (hBP : branchPageElement.Pgid.spec (GF := GF) (hG := hG))
    (hBK : branchPageElement.Key.spec (GF := GF) (hG := hG))
    (hSF : Inode.SetFlags.spec (GF := GF) (hG := hG))
    (hSK : Inode.SetKey.spec (GF := GF) (hG := hG))
    (hSV : Inode.SetValue.spec (GF := GF) (hG := hG))
    (hSP : Inode.SetPgid.spec (GF := GF) (hG := hG))
    (hK : Inode.Key.spec (GF := GF) (hG := hG))
    (hA : Assert.spec (GF := GF) (hG := hG)) :
    ReadInodeFromPage.spec (GF := GF) (hG := hG) := by
  intro l pg q Hc Hr
  obtain ⟨H16, Hleaf, Hbranch⟩ := Hr
  wp_start as Hpg
  have Hn16 : pageCount pg < 2 ^ 16 := leAt_lt pg 10 2
  have HcntZ : uint.Z (W16 (pageCount pg : Int)) = (pageCount pg : Int) := by
    have := toNat_W16 _ Hn16; word
  icases (page_header_bytes (hG := hG) l q pg H16 Hc).1 $$ Hpg with ⟨Hhd, Hrest⟩
  wp_auto
  wp_apply hCount $$ [$Hhd] as Hhd
  rw [HcntZ]
  wp_apply wp_slice_make2 (V := Inode) $$ [] as %s ⟨Hs, Hcap⟩
  · ipureintro; word
  try wp_auto
  wp_apply hLeaf $$ [$Hhd] as Hhd
  try wp_auto
  have HleafD : decide (W16 (pageFlags pg : Int) = W16 2) = decide (pageFlags pg = leafPageFlag) := by
    have Hf16 : pageFlags pg < 2 ^ 16 := leAt_lt pg 8 2
    unfold leafPageFlag
    simp only [decide_eq_decide]
    constructor
    · intro h; have := congrArg BitVec.toNat h; rw [toNat_W16 _ Hf16] at this; simpa using this
    · intro h; rw [h]; rfl
  rw [HleafD]
  ihave Hpg := (page_header_bytes (hG := hG) l q pg H16 Hc).2 $$ [Hhd Hrest]
  · iframe
  ihave %Hsl := ownSlice_len _ _ _ $$ Hs
  simp only [List.length_replicate] at Hsl
  ihave IH : (∃ (i : w64),
      "i" ∷ i_ptr ↦ i ∗ "inodes" ∷ inodes_ptr ↦ s ∗ "isLeaf" ∷ isLeaf_ptr ↦ decide (pageFlags pg = leafPageFlag) ∗
      "p" ∷ p_ptr ↦ l ∗ "Hpg" ∷ bytesPointsto l q pg ∗
      "Hs" ∷ s ↦* ((inodesOf l pg).take (sint.nat i) ++
        List.replicate (pageCount pg - sint.nat i) (zero_val Inode)) ∗
      "%Hi" ∷ ⌜0 ≤ sint.Z i ∧ sint.Z i ≤ (pageCount pg : Int)⌝ : IProp GF) $$ [i inodes isLeaf p Hpg Hs]
  · iexists W64 0
    simp only [named]
    iframe
    isplitl
    · rw [show sint.nat (W64 0) = 0 from rfl, List.take_zero, List.nil_append, Nat.sub_zero]
      rw [show sint.nat (W64 (pageCount pg : Int)) = pageCount pg by word]
      iexact Hs
    · ipureintro; constructor <;> word
  wp_for IH
  icases (page_header_bytes (hG := hG) l q pg H16 Hc).1 $$ Hpg with ⟨Hhd, Hrest⟩
  wp_apply hCount $$ [$Hhd] as Hhd
  ihave Hpg := (page_header_bytes (hG := hG) l q pg H16 Hc).2 $$ [Hhd Hrest]
  · iframe
  rw [HcntZ]
  try wp_auto
  wp_if_destruct
  · have Hb : decide (sint.Z i < sint.Z (W64 (pageCount pg : Int))) = true := by
      rw [go.intoVal_unfold Bool] at Hif; injection Hif with h; injection h
    have Hlt : sint.Z i < (pageCount pg : Int) := by
      have := of_decide_eq_true Hb; word
    rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨Hi.1, by word⟩)]
    try wp_auto
    have Hin : sint.nat i < pageCount pg := by word
    have Hi16 : uint.Z (W16 (sint.Z i)) = (sint.nat i : Int) := by word
    icases ownSlice_elem_acc (sint.Z i) (zero_val Inode) s (DFrac.own 1) _ Hi.1
      (by rw [show (sint.Z i).toNat = sint.nat i from rfl]
          exact prefix_fill_lookup _ _ _ _ Hin (inodesOf_length l pg)) $$ Hs with ⟨Hino, Hsw⟩
    by_cases HL : pageFlags pg = leafPageFlag
    · have HR := Hleaf HL
      unfold leafReadable leafWF at HR
      obtain ⟨⟨_, Hcnt, Hel, _⟩, Hks⟩ := HR
      obtain ⟨Hend, Hmax⟩ := Hel _ Hin
      have Hk0 := Hks _ Hin
      have Hroom : elemOff (sint.nat i) + 16 ≤ pg.length := by
        unfold elemOff at *; omega
      rw [decide_eq_true HL]
      try wp_auto
      wp_apply hLE
      rw [Hi16, show (16 : Int) + 16 * (sint.nat i : Int) = (elemOff (sint.nat i) : Int) by
        unfold elemOff; omega]
      try wp_auto
      icases (leafElem_in_page (hG := hG) l q pg (sint.nat i) Hroom Hc).1 $$ Hpg
        with ⟨Hpre, He, Hpost⟩
      have Hce : (l +ₗ (elemOff (sint.nat i) : Int)).locCar ≠ 0 := by simpa [Loc.add] using Hc
      have Hpos := leAt_lt pg (elemOff (sint.nat i) + 4) 4
      have Hksz := leAt_lt pg (elemOff (sint.nat i) + 8) 4
      have Hvsz := leAt_lt pg (elemOff (sint.nat i) + 12) 4
      have HposZ : uint.Z (leafElemOf pg (sint.nat i)).pos' = (leafPos pg (sint.nat i) : Int) := by
        unfold leafElemOf leafPos; simp only; have := toNat_W32 _ Hpos; word
      have HkszZ : uint.Z (leafElemOf pg (sint.nat i)).ksize' = (leafKsize pg (sint.nat i) : Int) := by
        unfold leafElemOf leafKsize; simp only; have := toNat_W32 _ Hksz; word
      have HvszZ : uint.Z (leafElemOf pg (sint.nat i)).vsize' = (leafVsize pg (sint.nat i) : Int) := by
        unfold leafElemOf leafVsize; simp only; have := toNat_W32 _ Hvsz; word
      wp_apply hLF $$ [$He] as He
      wp_apply hSF $$ [$Hino] as Hino
      try wp_auto
      wp_apply hLK _ _ _ Hce (by rw [HposZ, HkszZ]; omega) $$ [$He] as He
      wp_apply hSK $$ [$Hino] as Hino
      try wp_auto
      wp_apply hLV _ _ _ Hce (by rw [HposZ, HkszZ, HvszZ]; omega) $$ [$He] as He
      wp_apply hSV $$ [$Hino] as Hino
      try wp_auto
      have Hp' : uint.Z (W32 (leafPos pg (sint.nat i) : Int)) = (leafPos pg (sint.nat i) : Int) := by
        have := toNat_W32 _ Hpos; word
      have Hk' : uint.Z (W32 (leafKsize pg (sint.nat i) : Int)) = (leafKsize pg (sint.nat i) : Int) := by
        have := toNat_W32 _ Hksz; word
      have Hv' : uint.Z (W32 (leafVsize pg (sint.nat i) : Int)) = (leafVsize pg (sint.nat i) : Int) := by
        have := toNat_W32 _ Hvsz; word
      wp_apply hK $$ [$Hino] as Hino
      try wp_auto
      rw [Hp', Hk', Hv']
      rw [decide_eq_true (show sint.Z (W64 0) < sint.Z (W64 (leafKsize pg (sint.nat i) : Int)) by
        word)]
      wp_apply hA
      try wp_auto
      wp_for_post
      ihave Hs := Hsw $$ Hino
      ihave Hpg := (leafElem_in_page (hG := hG) l q pg (sint.nat i) Hroom Hc).2 $$ [Hpre He Hpost]
      · iframe
      iframe
      iexists i + W64 1
      iframe
      isplitl
      · rw [show sint.nat (i + W64 1) = sint.nat i + 1 by word,
          ← prefix_fill_set (inodesOf l pg) (zero_val Inode) (sint.nat i) (pageCount pg) Hin
            (inodesOf_length l pg)]
        iExactEq Hs
        congr 2
        rw [inodesOf_get l pg _ Hin]
        unfold inodeOf
        rw [ite_eq_left_of_eq_true _ _ (eq_true HL)]
        simp only [loc_add_assoc, Int.natCast_add, Int.add_assoc]
        rfl
      · ipureintro; constructor <;> word
    · have HR := Hbranch HL
      unfold branchReadable at HR
      obtain ⟨Hcnt, Hel⟩ := HR
      obtain ⟨Hend, Hmax, Hk0⟩ := Hel _ Hin
      have Hroom : elemOff (sint.nat i) + 16 ≤ pg.length := by
        unfold elemOff at *; omega
      rw [decide_eq_false HL]
      try wp_auto
      wp_apply hBE
      rw [Hi16, show (16 : Int) + 16 * (sint.nat i : Int) = (elemOff (sint.nat i) : Int) by
        unfold elemOff; omega]
      try wp_auto
      icases (branchElem_in_page (hG := hG) l q pg (sint.nat i) Hroom Hc).1 $$ Hpg
        with ⟨Hpre, He, Hpost⟩
      have Hce : (l +ₗ (elemOff (sint.nat i) : Int)).locCar ≠ 0 := by simpa [Loc.add] using Hc
      have Hpos := leAt_lt pg (elemOff (sint.nat i)) 4
      have Hksz := leAt_lt pg (elemOff (sint.nat i) + 4) 4
      have HposZ : uint.Z (branchElemOf pg (sint.nat i)).pos' = (branchPos pg (sint.nat i) : Int) := by
        unfold branchElemOf branchPos; simp only; have := toNat_W32 _ Hpos; word
      have HkszZ : uint.Z (branchElemOf pg (sint.nat i)).ksize' =
          (branchKsize pg (sint.nat i) : Int) := by
        unfold branchElemOf branchKsize; simp only; have := toNat_W32 _ Hksz; word
      wp_apply hBP $$ [$He] as He
      wp_apply hSP $$ [$Hino] as Hino
      try wp_auto
      wp_apply hBK _ _ _ Hce (by rw [HposZ, HkszZ]; omega) $$ [$He] as He
      wp_apply hSK $$ [$Hino] as Hino
      try wp_auto
      have Hp' : uint.Z (W32 (branchPos pg (sint.nat i) : Int)) = (branchPos pg (sint.nat i) : Int) := by
        have := toNat_W32 _ Hpos; word
      have Hk' : uint.Z (W32 (branchKsize pg (sint.nat i) : Int)) =
          (branchKsize pg (sint.nat i) : Int) := by
        have := toNat_W32 _ Hksz; word
      wp_apply hK $$ [$Hino] as Hino
      try wp_auto
      rw [Hp', Hk']
      rw [decide_eq_true (show sint.Z (W64 0) < sint.Z (W64 (branchKsize pg (sint.nat i) : Int)) by
        word)]
      wp_apply hA
      try wp_auto
      wp_for_post
      ihave Hs := Hsw $$ Hino
      ihave Hpg := (branchElem_in_page (hG := hG) l q pg (sint.nat i) Hroom Hc).2 $$ [Hpre He Hpost]
      · iframe
      iframe
      iexists i + W64 1
      iframe
      isplitl
      · rw [show sint.nat (i + W64 1) = sint.nat i + 1 by word,
          ← prefix_fill_set (inodesOf l pg) (zero_val Inode) (sint.nat i) (pageCount pg) Hin
            (inodesOf_length l pg)]
        iExactEq Hs
        congr 2
        rw [inodesOf_get l pg _ Hin]
        unfold inodeOf
        rw [ite_eq_right_of_eq_false _ _ (eq_false HL)]
        simp only [loc_add_assoc, Int.natCast_add, Int.add_assoc]
        rfl
      · ipureintro; constructor <;> word
  · have Hb : decide (sint.Z i < sint.Z (W64 (pageCount pg : Int))) = false := by
      cases h : decide (sint.Z i < sint.Z (W64 (pageCount pg : Int)))
      · rfl
      · exact absurd (by rw [h]) Hif
    have Hge : (pageCount pg : Int) ≤ sint.Z i := by
      have := of_decide_eq_false Hb; word
    have Heq : sint.nat i = pageCount pg := by word
    have Hft : ((#false : val) = #true) ↔ False := by
      constructor
      · intro h; rw [go.intoVal_unfold Bool] at h; injection h with h; injection h with h; cases h
      · exact False.elim
    rw [Hb]
    simp only [Hft, decide_false, Bool.false_eq_true, ↓reduceIte]
    try wp_auto
    rw [Heq, Nat.sub_self, List.replicate_zero, List.append_nil,
      List.take_of_length_le (by simp [inodesOf])]
    iapply HΦ; iframe

end proof

end bbolt
end EtcdGrove
end Perennial
