/-
The proof of `Spec/go_etcd_io/bbolt/Cursor__nsearch_p.lean` (U6, `notes/bbolt-proof-plan.md`):
`sort.Search` over the leaf page's elements, comparing each key (bytes of the page) with
`bytes.Compare`.
-/
module

public import Spec.go_etcd_io.bbolt.Cursor__nsearch_p
public import Spec.go_etcd_io.bbolt.internal.common.Page__LeafPageElements
public import Spec.go_etcd_io.bbolt.internal.common.Page__Count
public import Spec.go_etcd_io.bbolt.internal.common.leafPageElement__Key
public import Perennial.Spec.sort.Search
public import Perennial.Spec.bytes.Compare
public import Proof.go_etcd_io.bbolt.Read.Bytes
public import Proof.go_etcd_io.bbolt.Read.Search
public import Proof.go_etcd_io.bbolt.internal.common.Lemmas.Layout

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Fs

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]

variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- The search predicate of `nsearch` on a leaf page: key `i` is not below `kb`. -/
def npPred (pg : List w8) (kb : List w8) (i : Int) : Bool :=
  decide (¬ go.GoStringLt (leafKey pg i.toNat) kb)

theorem npPred_mono (pg : List w8) (kb : List w8)
    (hs : ∀ i j, i < j → j < pageCount pg → go.GoStringLt (leafKey pg i) (leafKey pg j)) :
    sort.IsMonoPred (npPred pg kb) (pageCount pg : Int) := by
  intro i j hij hi
  obtain ⟨h0, hij, hjn⟩ := hij
  simp only [npPred, decide_eq_true_eq] at hi ⊢
  intro hj
  apply hi
  have hlt := hs i.toNat j.toNat (by omega) (by omega)
  exact go.goStringLt_trans hlt hj

theorem Cursor.nsearch_p.wp_proof
    (hLE : internal.common.Page.LeafPageElements.spec (GF := GF) (hG := hG))
    (hCnt : internal.common.Page.Count.spec (GF := GF) (hG := hG))
    (hK : internal.common.leafPageElement.Key.spec (GF := GF) (hG := hG))
    (hS : sort.Search.spec (GF := GF) (hG := hG)) (hC : bytes.Compare.spec (GF := GF) (hG := hG)) :
    Cursor.nsearch_p.spec (GF := GF) (hG := hG) := by
  intro c b stk els e dq pg key dk kb hnode hleaf hwf
  wp_start as ⟨Hc, Hs, Hp, Hk⟩
  obtain ⟨hlenpg, hcnt, helems, hsorted⟩ := hwf
  have h16 : 16 ≤ pg.length := by unfold elemOff at hcnt; omega
  icases Read.bytesPointsto_bounds e.page' dq pg (by intro h; simp [h] at h16) $$ Hp
    with ⟨Hp, %Hpb⟩
  ihave %Hsl := ownSlice_len _ _ _ $$ Hs
  wp_auto
  have hidx : sint.Z (stk.len - W64 1) = (els.length : Int) := by
    simp only [List.length_append, List.length_singleton] at Hsl; word
  rw [if_pos (by rw [hidx]; word)]
  icases ownSlice_elem_acc (sint.Z (stk.len - W64 1)) e _ _ (els ++ [e]) (by omega)
    (by rw [hidx]; simp) $$ Hs with ⟨He, Hsback⟩
  rw [hidx]
  wp_auto
  rw [hnode]
  wp_auto
  icases bytesPointsto_view_read (V := Page) e.page' dq pg 0 e.page' (by simp) (by omega) Hpb.1
    $$ Hp with ⟨Hh, Hhb⟩
  rw [show (decode (List.take 16 (List.drop 0 pg)) : Page) = pageHdr pg from rfl]
  obtain ⟨hd, hH⟩ : ∃ hd, pageHdr pg = hd := ⟨_, rfl⟩
  have hcz : uint.Z hd.count' = (pageCount pg : Int) := by unfold pageCount; rw [hH]
  rw [hH]
  wp_apply hLE e.page' hd dq Hpb.1 (by unfold elemOff at hcnt; rw [hcz]; omega) $$ [Hh]
    as Hh
  · iexact Hh
  wp_apply hCnt e.page' hd dq $$ [Hh] as Hh
  · iexact Hh
  ihave Hp := Hhb $$ Hh
  have hcnt16 : pageCount pg < 2 ^ 16 := by unfold pageCount; exact BitVec.isLt _
  have hn : sint.Z (W64 (uint.Z hd.count')) = (pageCount pg : Int) := by rw [hcz]; word
  wp_apply hS (W64 (uint.Z hd.count')) _ (npPred pg kb)
    iprop(key_ptr ↦ key ∗
      inodes_ptr ↦ (if hd.count' = W16 0 then slice.nil else slice.mk (e.page' +ₗ 16)
        (W64 (uint.Z hd.count')) (W64 (uint.Z hd.count'))) ∗
      key ↦*{dk} kb ∗ bytesPointsto e.page' dq pg) $$ [key inodes Hk Hp]
  · iframe
    isplitl []
    · ipureintro; word
    isplitl []
    · unfold sort.predImplements
      iintro %i
      wp_start as ⟨⟨Hkp, Hin, Hk, Hp⟩, %Hb⟩
      rw [hn] at Hb
      have hcnz : hd.count' ≠ W16 0 := by
        intro h
        have : (pageCount pg : Int) = 0 := by rw [← hcz, h]; rfl
        omega
      rw [if_neg hcnz]
      wp_auto
      rw [if_pos ⟨Hb.1, by rw [hn]; exact Hb.2⟩]
      obtain ⟨k, hk⟩ : ∃ k : Nat, sint.Z i = (k : Int) := ⟨(sint.Z i).toNat, by omega⟩
      have hkc : k < pageCount pg := by omega
      have hloc : sliceIndexRef leafPageElement (sint.Z i)
          (slice.mk (e.page' +ₗ 16) (W64 (uint.Z hd.count')) (W64 (uint.Z hd.count'))) =
          e.page' +ₗ ((elemOff k : Nat) : Int) := by
        rw [sliceIndexRef_plain leafPageElement.ty leafPageElement.layout _ i
          (by simp [Loc.add]; omega) Hb.1]
        simp only [sint.nat, hk, Int.toNat_natCast, loc_add_assoc, elemOff]
        congr 1; push_cast; omega
      rw [hloc]
      obtain ⟨he1, he2⟩ := helems k hkc
      icases bytesPointsto_view_read (V := leafPageElement) e.page' dq pg (elemOff k)
        (e.page' +ₗ ((elemOff k : Nat) : Int)) rfl (by unfold elemOff at hcnt ⊢; omega) Hpb.1
        $$ Hp with ⟨Hel, Helb⟩
      rw [show (decode (List.take 16 (List.drop (elemOff k) pg)) : leafPageElement) =
        leafElem pg k from rfl]
      obtain ⟨le, hle⟩ : ∃ le, leafElem pg k = le := ⟨_, rfl⟩
      have hpos : uint.Z le.pos' = (leafPos pg k : Int) := by unfold leafPos; rw [hle]
      have hks : uint.Z le.ksize' = (leafKsize pg k : Int) := by unfold leafKsize; rw [hle]
      rw [hle]
      wp_apply hK (e.page' +ₗ ((elemOff k : Nat) : Int)) le dq (by simp [Loc.add]; omega)
        (by simp only [Loc.add]; rw [hpos, hks]; omega) $$ [Hel] as Hel
      · iexact Hel
      ihave Hp := Helb $$ Hel
      have hkl : (leafKey pg k).length = leafKsize pg k := by
        unfold leafKey bytesAt; simp only [List.length_take, List.length_drop]; omega
      icases Read.bytesPointsto_sub_acc e.page' dq pg (leafKey pg k) (elemOff k + leafPos pg k)
        (by rw [hkl]; omega) (by rw [hkl]; rfl) $$ Hp with ⟨Hkb, Hpb2⟩
      have hkloc : (e.page' +ₗ ((elemOff k : Nat) : Int)) +ₗ uint.Z le.pos' =
          e.page' +ₗ ((elemOff k + leafPos pg k : Nat) : Int) := by
        rw [loc_add_assoc, hpos]; push_cast; rfl
      have hksz : W64 (uint.Z le.ksize') = W64 ((leafKey pg k).length : Int) := by rw [hks, hkl]
      rw [hkloc, hksz]
      icases (Read.bytesPointsto_ownSlice (e.page' +ₗ ((elemOff k + leafPos pg k : Nat) : Int)) dq
        (leafKey pg k) (by simp [Loc.add]; omega) (by rw [hkl]; unfold maxAllocSize at he2; omega)).1
        $$ Hkb with Hkb
      wp_apply hC $$ [Hkb Hk] as ⟨Hkb, Hk⟩
      · iframe
      try wp_auto
      icases (Read.bytesPointsto_ownSlice (e.page' +ₗ ((elemOff k + leafPos pg k : Nat) : Int)) dq
        (leafKey pg k) (by simp [Loc.add]; omega) (by rw [hkl]; unfold maxAllocSize at he2; omega)).2
        $$ Hkb with Hkb
      ihave Hp := Hpb2 $$ Hkb
      iapply HΦ
      iframe
      ipureintro
      simp only [npPred, hk, Int.toNat_natCast, bytes.compareResult]
      by_cases hlt : go.GoStringLt (leafKey pg k) kb
      · simp [hlt]
      · simp only [hlt, ↓reduceIte]
        split <;> decide
    ipureintro; rw [hn]; exact npPred_mono pg kb hsorted
  iintro %idx ⟨⟨Hkp, Hin, Hk, Hp⟩, %H0, %Hfound, %Hoob, %Hgt⟩
  rw [hn] at Hfound Hoob
  have Hle : sint.Z idx ≤ (pageCount pg : Int) := by
    rcases Int.lt_or_le (pageCount pg : Int) (sint.Z idx) with hc | hc
    · have := Hoob (fun k hk => Hgt k ⟨hk.1, by omega⟩)
      omega
    · exact hc
  have Hidx : pageSeekIdx pg kb = sint.nat idx := by
    unfold pageSeekIdx
    apply Read.takeWhile_range_length _ _ _ (by word)
    · intro k hk
      have := Hgt (k : Int) ⟨by omega, by word⟩
      simpa [npPred] using this
    · intro hk
      have := Hfound (by word)
      simpa [npPred, show ((sint.Z idx).toNat) = sint.nat idx from rfl] using this
  wp_auto
  ihave Hs := Hsback $$ He
  have hW : W64 (pageSeekIdx pg kb : Int) = idx := by rw [Hidx]; word
  rw [hW, hnode]
  rw [show (els ++ [e]).set (↑els.length : Int).toNat
      ({ page' := e.page', node' := null, index' := idx } : elemRef) =
      els ++ [{ page' := e.page', node' := null, index' := idx }] by simp]
  iapply HΦ
  iframe

end proof

end bbolt
end EtcdGrove
end Perennial
