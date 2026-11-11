/-
`ReadInodeFromPage`'s proof (`internal/common/inode.go`): a stub, proved by U1 of
`notes/bbolt-proof-plan.md`.
-/
module

public import Spec.go_etcd_io.bbolt.internal.common.ReadInodeFromPage
public import Proof.go_etcd_io.bbolt.internal.common.Lemmas.Layout
public import Spec.go_etcd_io.bbolt.internal.common.Assert
public import Spec.go_etcd_io.bbolt.internal.common.Inode__SetPgid
public import Spec.go_etcd_io.bbolt.internal.common.Inode__SetFlags
public import Spec.go_etcd_io.bbolt.internal.common.Inode__SetValue
public import Spec.go_etcd_io.bbolt.internal.common.Inode__SetKey
public import Spec.go_etcd_io.bbolt.internal.common.Inode__Key
public import Spec.go_etcd_io.bbolt.internal.common.branchPageElement__Pgid
public import Spec.go_etcd_io.bbolt.internal.common.branchPageElement__Key
public import Spec.go_etcd_io.bbolt.internal.common.leafPageElement__Flags
public import Spec.go_etcd_io.bbolt.internal.common.leafPageElement__Value
public import Spec.go_etcd_io.bbolt.internal.common.leafPageElement__Key
public import Spec.go_etcd_io.bbolt.internal.common.Page__BranchPageElement
public import Spec.go_etcd_io.bbolt.internal.common.Page__LeafPageElement
public import Spec.go_etcd_io.bbolt.internal.common.Page__IsLeafPage
public import Spec.go_etcd_io.bbolt.internal.common.Page__Count

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Fs
namespace internal
namespace common

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt.internal.common

/-- One iteration of `ReadInodeFromPage`'s loop: inode `j` replaces the zero at `j`. -/
theorem readInodes_step {α : Type} (L : List α) (n j : Nat) (z : α) (hL : L.length = n)
    (hj : j < n) {v : α} (hv : L[j]'(by omega) = v) :
    (L.take j ++ List.replicate (n - j) z).set j v = L.take (j + 1) ++ List.replicate (n - (j + 1)) z := by
  subst hv
  have hlen : (L.take j).length = j := by simp; omega
  obtain ⟨k, hk⟩ : ∃ k, n - j = k + 1 := ⟨n - j - 1, by omega⟩
  rw [hk, List.set_append_right _ _ (by omega), hlen, Nat.sub_self, List.replicate_succ,
    List.set_cons_zero, List.take_add_one, List.getElem?_eq_getElem (by omega)]
  simp only [Option.toList_some, List.append_assoc, List.singleton_append]
  congr 3; omega

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.internal.common.Assumptions]

theorem ReadInodeFromPage.wp_proof
    (wp_Page_Count : Page.Count.spec (GF := GF) (hG := hG))
    (wp_Page_IsLeafPage : Page.IsLeafPage.spec (GF := GF) (hG := hG))
    (wp_Page_LeafPageElement : Page.LeafPageElement.spec (GF := GF) (hG := hG))
    (wp_Page_BranchPageElement : Page.BranchPageElement.spec (GF := GF) (hG := hG))
    (wp_leafPageElement_Key : leafPageElement.Key.spec (GF := GF) (hG := hG))
    (wp_leafPageElement_Value : leafPageElement.Value.spec (GF := GF) (hG := hG))
    (wp_leafPageElement_Flags : leafPageElement.Flags.spec (GF := GF) (hG := hG))
    (wp_branchPageElement_Key : branchPageElement.Key.spec (GF := GF) (hG := hG))
    (wp_branchPageElement_Pgid : branchPageElement.Pgid.spec (GF := GF) (hG := hG))
    (wp_Inode_Key : Inode.Key.spec (GF := GF) (hG := hG))
    (wp_Inode_SetKey : Inode.SetKey.spec (GF := GF) (hG := hG))
    (wp_Inode_SetValue : Inode.SetValue.spec (GF := GF) (hG := hG))
    (wp_Inode_SetFlags : Inode.SetFlags.spec (GF := GF) (hG := hG))
    (wp_Inode_SetPgid : Inode.SetPgid.spec (GF := GF) (hG := hG))
    (wp_Assert : Assert.spec (GF := GF) (hG := hG)) :
    ReadInodeFromPage.spec (GF := GF) (hG := hG) := by
  intro p pg dq Hr Hp0 Hend
  obtain ⟨Hlen, Hel⟩ := Hr
  have hlen16 : 0 + 16 ≤ pg.length := by simp only [elemOff] at Hlen; omega
  wp_start as Hb
  icases bytesPointsto_view_read (V := Page) p dq pg 0 p (by simp [loc_add_0]) hlen16 Hp0 $$ Hb
    with ⟨Hh, Hclose⟩
  rw [show (decode ((pg.drop 0).take 16) : Page) = pageHdr pg from rfl]
  have hcnt : uint.Z (pageHdr pg).count' = pageCount pg := by simp [pageCount, uint.Z]
  have hcntlt : pageCount pg < 2 ^ 16 := by
    have := (pageHdr pg).count'.isLt; simp only [pageCount]; omega
  have hfl : ((pageHdr pg).flags' = W16 2) ↔ pageFlags pg = leafPageFlag := by
    simp only [pageFlags, leafPageFlag]; constructor <;> intro h
    · rw [h]; rfl
    · apply BitVec.eq_of_toNat_eq; rw [h]; rfl
  generalize hH : pageHdr pg = hdr at *
  wp_auto
  wp_apply wp_Page_Count $$ [$Hh] as Hh
  have hn : sint.nat (W64 (uint.Z hdr.count')) = pageCount pg := by
    rw [hcnt]; simp only [sint.nat]; word
  wp_apply wp_slice_make2 (V := Inode) $$ [] as %sl ⟨Hsl, Hcap⟩
  · ipureintro; rw [hcnt]; word
  rw [hn]
  wp_apply wp_Page_IsLeafPage $$ [$Hh] as Hh
  ihave %Hsll := ownSlice_len _ _ _ $$ Hsl
  simp only [List.length_replicate] at Hsll
  have hslZ : sint.Z sl.len = pageCount pg := by
    obtain ⟨h1, h2⟩ := Hsll; simp only [sint.nat, sint.Z] at h1 h2 ⊢; omega
  ihave HI : (∃ (i : w64),
      "i" ∷ i_ptr ↦ i ∗
      "inodes" ∷ inodes_ptr ↦ sl ∗
      "Hsl" ∷ sl ↦* ((pageInodesAt p pg).take (sint.nat i) ++
        List.replicate (pageCount pg - sint.nat i) (zero_val Inode)) ∗
      "Hcap" ∷ ownSliceCap Inode sl (DFrac.own 1) ∗
      "Hh" ∷ p ↦{dq} hdr ∗
      "Hclose" ∷ (p ↦{dq} hdr -∗ bytesPointsto p dq pg) ∗
      "HΦ" ∷ (∀ s, bytesPointsto p dq pg ∗ s ↦* pageInodesAt p pg ∗
        ownSliceCap Inode s (DFrac.own 1) -∗ Φ #s) ∗
      "«$res0»" ∷ «$res0_ptr» ↦ zero_val GoSlice ∗
      "p" ∷ p_ptr ↦ p ∗
      "isLeaf" ∷ isLeaf_ptr ↦ decide (hdr.flags' = W16 2) ∗
      "%Hi" ∷ ⌜0 ≤ sint.Z i ∧ sint.Z i ≤ pageCount pg⌝ : IProp GF)
    $$ [i inodes Hsl Hcap Hh Hclose HΦ «$res0» p isLeaf]
  · iexists (W64 0)
    rw [show sint.nat (W64 0) = 0 from rfl, List.take_zero, List.nil_append, Nat.sub_zero]
    iframe
    ipureintro; exact ⟨by decide, by simp⟩
  wp_for HI
  wp_apply wp_Page_Count $$ [$Hh] as Hh
  have hcW : sint.Z (W64 (uint.Z hdr.count')) = pageCount pg := by rw [hcnt]; word
  rw [hcW]
  have hiZ : sint.Z i = (sint.nat i : Int) := by
    simp only [sint.nat]; rw [Int.toNat_of_nonneg Hi.1]
  by_cases hexit : sint.Z i < pageCount pg
  · rw [decide_eq_true hexit]
    simp only [_root_.decide_true, ↓reduceIte]
    wp_auto
    have hin : sint.nat i < pageCount pg := by omega
    rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨Hi.1, by omega⟩)]
    have hlen' : ((pageInodesAt p pg).take (sint.nat i) ++
        List.replicate (pageCount pg - sint.nat i) (zero_val Inode)).length = pageCount pg := by
      simp [pageInodesAt]; omega
    have hlk : ((pageInodesAt p pg).take (sint.nat i) ++
        List.replicate (pageCount pg - sint.nat i) (zero_val Inode))[(sint.Z i).toNat]? =
          some (zero_val Inode) := by
      rw [show (sint.Z i).toNat = sint.nat i from rfl,
        List.getElem?_append_right (by simp [pageInodesAt]; try omega), List.getElem?_replicate]
      simp [pageInodesAt]; omega
    icases ownSlice_elem_acc (sint.Z i) (zero_val Inode) sl _ _ Hi.1 hlk $$ Hsl with ⟨Hq, Hsl⟩
    generalize sliceIndexRef Inode (sint.Z i) sl = q at *
    wp_auto
    have hiW : uint.Z (W16 (sint.Z i)) = sint.nat i := by
      rw [hiZ]; simp only [uint.Z]; word
    have hEnd := Hend _ hin
    have hEl := Hel _ hin
    have hle : elemOff (sint.nat i) + 16 ≤ pg.length := by
      simp only [elemOff] at Hlen ⊢; omega
    wp_if_destruct
    · -- a leaf page
      have hL : pageFlags pg = leafPageFlag := hfl.1 Hif
      simp only [elemEnd, hL, ↓reduceIte] at hEnd hEl
      wp_apply wp_Page_LeafPageElement
      · ipureintro; exact Hp0
      · ipureintro; rw [hiW]; simp only [elemOff] at hEnd; omega
      rw [hiW]
      ispecialize Hclose $$ Hh
      icases bytesPointsto_view_read (V := leafPageElement) p dq pg (elemOff (sint.nat i))
        (p +ₗ (16 + 16 * (sint.nat i : Int))) (by simp only [elemOff]; congr 1; try omega) hle Hp0
        $$ Hclose with ⟨He, Hclose⟩
      rw [show (decode ((pg.drop (elemOff (sint.nat i))).take 16) : leafPageElement) =
        leafElem pg (sint.nat i) from rfl]
      have hpos : uint.Z (leafElem pg (sint.nat i)).pos' = leafPos pg (sint.nat i) := by
        simp [leafPos, uint.Z]
      have hks : uint.Z (leafElem pg (sint.nat i)).ksize' = leafKsize pg (sint.nat i) := by
        simp [leafKsize, uint.Z]
      have hvs : uint.Z (leafElem pg (sint.nat i)).vsize' = leafVsize pg (sint.nat i) := by
        simp [leafVsize, uint.Z]
      have hea : (p +ₗ (16 + 16 * (sint.nat i : Int))).addr = p.addr + elemOff (sint.nat i) := by
        simp only [Loc.add, elemOff]; omega
      generalize he : leafElem pg (sint.nat i) = e at *
      wp_apply wp_leafPageElement_Flags (p +ₗ (16 + 16 * (sint.nat i : Int))) e dq $$ [He] as He
      · iexact He
      wp_apply wp_Inode_SetFlags $$ [$Hq] as Hq
      wp_apply wp_leafPageElement_Key (p +ₗ (16 + 16 * (sint.nat i : Int))) e dq
        (by rw [hea]; omega) (by rw [hea, hpos, hks]; omega) $$ [He] as He
      · iexact He
      wp_apply wp_Inode_SetKey $$ [$Hq] as Hq
      wp_apply wp_leafPageElement_Value (p +ₗ (16 + 16 * (sint.nat i : Int))) e dq
        (by rw [hea]; omega) (by rw [hea, hpos, hks, hvs]; omega) $$ [He] as He
      · iexact He
      wp_apply wp_Inode_SetValue $$ [$Hq] as Hq
      wp_apply wp_Inode_Key $$ [$Hq] as Hq
      have hkpos : sint.Z (W64 0) < sint.Z (W64 (uint.Z e.ksize')) := by
        have := e.ksize'.isLt
        rw [hks]; have h1 := hEl.1; simp only [maxAllocSize] at hEl; word
      rw [decide_eq_true hkpos]
      wp_apply wp_Assert
      have hV : (⟨e.flags', 0,
            slice.mk (p +ₗ (16 + 16 * (sint.nat i : Int)) +ₗ uint.Z e.pos')
              (W64 (uint.Z e.ksize')) (W64 (uint.Z e.ksize')),
            slice.mk (p +ₗ (16 + 16 * (sint.nat i : Int)) +ₗ (uint.Z e.pos' + uint.Z e.ksize'))
              (W64 (uint.Z e.vsize')) (W64 (uint.Z e.vsize'))⟩ : Inode) =
          pageInodeAt p pg (sint.nat i) := by
        simp only [pageInodeAt, hL, ↓reduceIte, keySliceAt, valSliceAt, bslice, he, loc_add_assoc,
          hpos, hks, hvs, elemOff]
        congr 3 <;> (try congr 1) <;> omega
      ihave Hq : q ↦ pageInodeAt p pg (sint.nat i) $$ [Hq]
      · rw [← hV]; iexact Hq
      ispecialize Hsl $$ Hq
      ispecialize Hclose $$ He
      icases bytesPointsto_view_read (V := Page) p dq pg 0 p (by simp [loc_add_0]) hlen16 Hp0
        $$ Hclose with ⟨Hh, Hclose⟩
      rw [show (decode ((pg.drop 0).take 16) : Page) = pageHdr pg from rfl, hH]
      wp_for_post
      have hi1 : sint.nat (i + W64 1) = sint.nat i + 1 := by
        have := Hi.2; simp only [sint.nat, sint.Z] at this hexit ⊢; word
      iexists (i + W64 1)
      rw [hi1, show (sint.Z i).toNat = sint.nat i from rfl,
        readInodes_step _ _ _ _ (by simp [pageInodesAt]) hin (by simp [pageInodesAt, List.getElem_map])]
      iframe
      ipureintro
      have := Hi.2; simp only [sint.nat, sint.Z] at this hexit hi1 ⊢; word
    · -- a branch page
      have hB : ¬ pageFlags pg = leafPageFlag := fun h => Hif (hfl.2 h)
      simp only [elemEnd, hB, ↓reduceIte] at hEnd hEl
      wp_apply wp_Page_BranchPageElement
      · ipureintro; exact Hp0
      · ipureintro; rw [hiW]; simp only [elemOff] at hEnd; omega
      rw [hiW]
      ispecialize Hclose $$ Hh
      icases bytesPointsto_view_read (V := branchPageElement) p dq pg (elemOff (sint.nat i))
        (p +ₗ (16 + 16 * (sint.nat i : Int))) (by simp only [elemOff]; congr 1; try omega) hle Hp0
        $$ Hclose with ⟨He, Hclose⟩
      rw [show (decode ((pg.drop (elemOff (sint.nat i))).take 16) : branchPageElement) =
        branchElem pg (sint.nat i) from rfl]
      have hpos : uint.Z (branchElem pg (sint.nat i)).pos' = branchPos pg (sint.nat i) := by
        simp [branchPos, uint.Z]
      have hks : uint.Z (branchElem pg (sint.nat i)).ksize' = branchKsize pg (sint.nat i) := by
        simp [branchKsize, uint.Z]
      have hea : (p +ₗ (16 + 16 * (sint.nat i : Int))).addr = p.addr + elemOff (sint.nat i) := by
        simp only [Loc.add, elemOff]; omega
      generalize he : branchElem pg (sint.nat i) = e at *
      wp_apply wp_branchPageElement_Pgid (p +ₗ (16 + 16 * (sint.nat i : Int))) e dq $$ [He] as He
      · iexact He
      wp_apply wp_Inode_SetPgid $$ [$Hq] as Hq
      wp_apply wp_branchPageElement_Key (p +ₗ (16 + 16 * (sint.nat i : Int))) e dq
        (by rw [hea]; omega) (by rw [hea, hpos, hks]; omega) $$ [He] as He
      · iexact He
      wp_apply wp_Inode_SetKey $$ [$Hq] as Hq
      wp_apply wp_Inode_Key $$ [$Hq] as Hq
      have hkpos : sint.Z (W64 0) < sint.Z (W64 (uint.Z e.ksize')) := by
        have := e.ksize'.isLt
        rw [hks]; have h1 := hEl.1; simp only [maxAllocSize] at hEl; word
      rw [decide_eq_true hkpos]
      wp_apply wp_Assert
      have hV : (⟨0, e.pgid',
            slice.mk (p +ₗ (16 + 16 * (sint.nat i : Int)) +ₗ uint.Z e.pos')
              (W64 (uint.Z e.ksize')) (W64 (uint.Z e.ksize')), slice.nil⟩ : Inode) =
          pageInodeAt p pg (sint.nat i) := by
        simp only [pageInodeAt, hB, ↓reduceIte, keySliceAt, bslice, he, loc_add_assoc,
          hpos, hks, elemOff]
        congr 3 <;> (try congr 1) <;> omega
      ihave Hq : q ↦ pageInodeAt p pg (sint.nat i) $$ [Hq]
      · rw [← hV]; iexact Hq
      ispecialize Hsl $$ Hq
      ispecialize Hclose $$ He
      icases bytesPointsto_view_read (V := Page) p dq pg 0 p (by simp [loc_add_0]) hlen16 Hp0
        $$ Hclose with ⟨Hh, Hclose⟩
      rw [show (decode ((pg.drop 0).take 16) : Page) = pageHdr pg from rfl, hH]
      wp_for_post
      have hi1 : sint.nat (i + W64 1) = sint.nat i + 1 := by
        have := Hi.2; simp only [sint.nat, sint.Z] at this hexit ⊢; word
      iexists (i + W64 1)
      rw [hi1, show (sint.Z i).toNat = sint.nat i from rfl,
        readInodes_step _ _ _ _ (by simp [pageInodesAt]) hin (by simp [pageInodesAt, List.getElem_map])]
      iframe
      ipureintro
      have := Hi.2; simp only [sint.nat, sint.Z] at this hexit hi1 ⊢; word
  · rw [decide_eq_false hexit]
    simp only [show decide ((#false : val) = #true) = false from decide_eq_false (by
      intro h; have := GoGlobalContext.intoVal_inj_bool h; simp at this), Bool.false_eq_true, _root_.decide_true, ↓reduceIte]
    wp_auto
    have hin : sint.nat i = pageCount pg := by
      have := Hi.2; simp only [sint.nat, sint.Z] at this hexit ⊢; omega
    rw [hin, Nat.sub_self, List.replicate_zero, List.append_nil,
      List.take_of_length_le (by simp [pageInodesAt])]
    iapply HΦ
    iframe
    iapply Hclose $$ Hh

end proof

end common
end internal
end bbolt
end EtcdGrove
end Perennial
