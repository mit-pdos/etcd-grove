/-
The proof of `Spec/go_etcd_io/bbolt/Cursor__keyValue_r.lean` (U6, `notes/bbolt-proof-plan.md`):
the top element's `count()` (its page's header), then the leaf element's key, value and flags;
the slices' sources from `rd_src`.
-/
module

public import Spec.go_etcd_io.bbolt.Cursor__keyValue_r
public import Spec.go_etcd_io.bbolt.internal.common.Page__Count
public import Spec.go_etcd_io.bbolt.internal.common.Page__LeafPageElement
public import Spec.go_etcd_io.bbolt.internal.common.leafPageElement__Key
public import Spec.go_etcd_io.bbolt.internal.common.leafPageElement__Value
public import Spec.go_etcd_io.bbolt.internal.common.leafPageElement__Flags

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [hos : HasExt osFsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

theorem Cursor.keyValue_r.wp_proof
    (hCnt : internal.common.Page.Count.spec (GF := GF) (hG := hG))
    (hLPE : internal.common.Page.LeafPageElement.spec (GF := GF) (hG := hG))
    (hK : internal.common.leafPageElement.Key.spec (GF := GF) (hG := hG))
    (hV : internal.common.leafPageElement.Value.spec (GF := GF) (hG := hG))
    (hF : internal.common.leafPageElement.Flags.spec (GF := GF) (hG := hG)) :
    Cursor.keyValue_r.spec (GF := GF) (hG := hG) := by
  intro K tx src q T v b dq bv ibp pp c stk els e pid pg hpa hnode hleaf hwf h16 hi0
  wp_start as ⟨Hk, Hb, Hc, Hs⟩
  obtain ⟨-, hcnt, helems, -⟩ := hwf
  ihave #Hcom : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.common $$ []
  · iPkgInit
  icases rd_page_bounds K tx src q T v b dq bv ibp pp pid e.page' pg hpa
    (by intro h; simp [h] at h16) $$ [Hk Hb] with ⟨⟨Hk, Hb⟩, %Hpb⟩
  · iframe
  ihave %Hsl := ownSlice_len _ _ _ $$ Hs
  wp_auto
  have hidx : sint.Z (stk.len - W64 1) = (els.length : Int) := by
    simp only [List.length_append, List.length_singleton] at Hsl; word
  rw [if_pos (by rw [hidx]; word)]
  icases ownSlice_elem_acc (sint.Z (stk.len - W64 1)) e _ _ (els ++ [e]) (by omega)
    (by rw [hidx]; simp) $$ Hs with ⟨He, Hsback⟩
  rw [hidx]
  wp_auto
  wp_method_call; wp_call
  wp_auto
  rw [hnode]
  wp_auto
  icases rd_hdr_acc K tx src q T v b dq bv ibp pp pid e.page' pg hpa h16 $$ [Hk Hb]
    with ⟨%dqh, Hh, Hhb⟩
  · iframe
  obtain ⟨hd, hH⟩ : ∃ hd, pageHdr pg = hd := ⟨_, rfl⟩
  have hcz : uint.Z hd.count' = (pageCount pg : Int) := by unfold pageCount; rw [hH]
  have hcnt16 : pageCount pg < 2 ^ 16 := by unfold pageCount; exact BitVec.isLt _
  rw [hH]
  wp_apply hCnt e.page' hd dqh $$ [Hh] as Hh
  · iexact Hh
  by_cases hc0 : pageCount pg = 0
  · have : W64 (uint.Z hd.count') = W64 0 := by rw [hcz, hc0]; rfl
    rw [this]
    wp_auto
    ihave Hkb := Hhb $$ Hh
    icases Hkb with ⟨Hk, Hb⟩
    ihave Hs := Hsback $$ He
    rw [show (els ++ [e]).set (↑els.length : Int).toNat e = els ++ [e] by simp]
    iapply HΦ
    iframe
    unfold rKV
    rw [if_neg (by omega)]
    ipureintro; exact ⟨rfl, rfl, rfl⟩
  have hne : W64 (uint.Z hd.count') ≠ W64 0 := by
    rw [hcz]; intro h; apply hc0; have := congrArg BitVec.toNat h; simp at this; omega
  rw [decide_eq_false hne]
  wp_auto
  wp_method_call; wp_call
  wp_auto
  rw [hnode]
  wp_auto
  wp_apply hCnt e.page' hd dqh $$ [Hh] as Hh
  · iexact Hh
  have hcn : sint.Z (W64 (uint.Z hd.count')) = (pageCount pg : Int) := by rw [hcz]; word
  rw [hcn]
  by_cases hge : (pageCount pg : Int) ≤ sint.Z e.index'
  · rw [decide_eq_true hge]
    wp_auto
    ihave Hkb := Hhb $$ Hh
    icases Hkb with ⟨Hk, Hb⟩
    ihave Hs := Hsback $$ He
    rw [show (els ++ [e]).set (↑els.length : Int).toNat e = els ++ [e] by simp]
    iapply HΦ
    iframe
    unfold rKV
    rw [if_neg (by omega)]
    ipureintro; exact ⟨rfl, rfl, rfl⟩
  rw [decide_eq_false hge]
  wp_auto
  rw [hnode]
  wp_auto
  ihave Hkb := Hhb $$ Hh
  icases Hkb with ⟨Hk, Hb⟩
  obtain ⟨i, hi⟩ : ∃ i : Nat, sint.Z e.index' = (i : Int) := ⟨(sint.Z e.index').toNat, by omega⟩
  have hic : i < pageCount pg := by omega
  have hu : uint.Z (W16 (sint.Z e.index')) = (i : Int) := by rw [hi]; word
  wp_apply hLPE e.page' (W16 (sint.Z e.index')) Hpb.1
    (by rw [hu]; unfold elemOff at hcnt; omega)
  rw [hu]
  have hoff : (16 + 16 * (i : Int)) = ((elemOff i : Nat) : Int) := by unfold elemOff; push_cast; rfl
  rw [hoff]
  obtain ⟨he1, he2⟩ := helems i hic
  icases rd_elem_acc (V := leafPageElement) K tx src q T v b dq bv ibp pp pid e.page' pg hpa i
    (by unfold elemOff at hcnt ⊢; omega) $$ [Hk Hb] with ⟨%dqe, Hel, Helb⟩
  · iframe
  rw [show (decode (bytesAt pg (elemOff i) 16) : leafPageElement) = leafElem pg i from rfl]
  obtain ⟨le, hle⟩ : ∃ le, leafElem pg i = le := ⟨_, rfl⟩
  have hpos : uint.Z le.pos' = (leafPos pg i : Int) := by unfold leafPos; rw [hle]
  have hks : uint.Z le.ksize' = (leafKsize pg i : Int) := by unfold leafKsize; rw [hle]
  have hvs : uint.Z le.vsize' = (leafVsize pg i : Int) := by unfold leafVsize; rw [hle]
  rw [hle]
  have hea : 0 < (e.page' +ₗ ((elemOff i : Nat) : Int)).addr := by simp [Loc.add]; omega
  wp_apply hK (e.page' +ₗ ((elemOff i : Nat) : Int)) le dqe hea
    (by simp only [Loc.add]; rw [hpos, hks]; omega) $$ [Hel] as Hel
  · iexact Hel
  try wp_auto
  wp_apply hV (e.page' +ₗ ((elemOff i : Nat) : Int)) le dqe hea
    (by simp only [Loc.add]; rw [hpos, hks, hvs]; omega) $$ [Hel] as Hel
  · iexact Hel
  try wp_auto
  wp_apply hF (e.page' +ₗ ((elemOff i : Nat) : Int)) le dqe $$ [Hel] as Hel
  · iexact Hel
  try wp_auto
  ihave Hkb := Helb $$ Hel
  have hk32 : leafKsize pg i < 2 ^ 32 := by unfold leafKsize; exact BitVec.isLt _
  have hv32 : leafVsize pg i < 2 ^ 32 := by unfold leafVsize; exact BitVec.isLt _
  icases rd_src K tx src q T v b dq bv ibp pp pid e.page' pg hpa (by intro h; simp [h] at h16)
    (elemOff i + leafPos pg i) (leafKsize pg i) (by omega) hk32 $$ Hkb with ⟨Hkb, %ks, %hks0, #Hks⟩
  icases rd_src K tx src q T v b dq bv ibp pp pid e.page' pg hpa (by intro h; simp [h] at h16)
    (elemOff i + leafPos pg i + leafKsize pg i) (leafVsize pg i) (by omega) hv32 $$ Hkb
    with ⟨⟨Hk, Hb⟩, %vs, %hvs0, #Hvs⟩
  ihave Hs := Hsback $$ He
  rw [show (els ++ [e]).set (↑els.length : Int).toNat e = els ++ [e] by simp]
  have hkloc : (e.page' +ₗ ((elemOff i : Nat) : Int)) +ₗ uint.Z le.pos' =
      e.page' +ₗ ((elemOff i + leafPos pg i : Nat) : Int) := by
    rw [loc_add_assoc, hpos]; push_cast; rfl
  have hvloc : (e.page' +ₗ ((elemOff i : Nat) : Int)) +ₗ (uint.Z le.pos' + uint.Z le.ksize') =
      e.page' +ₗ ((elemOff i + leafPos pg i + leafKsize pg i : Nat) : Int) := by
    rw [loc_add_assoc, hpos, hks]; push_cast; rw [Int.add_assoc]
  rw [hkloc, hvloc, hks, hvs]
  iapply HΦ
  iframe
  unfold rKV
  rw [hi, Int.toNat_natCast, if_pos hic]
  rw [show leafKey pg i = bytesAt pg (elemOff i + leafPos pg i) (leafKsize pg i) from rfl,
    show leafValue pg i = bytesAt pg (elemOff i + leafPos pg i + leafKsize pg i) (leafVsize pg i)
      from rfl]
  iexists ks, vs
  isplitr
  · ipureintro; exact ⟨hks0, hvs0, by rw [hle]⟩
  isplitl
  · iexact Hks
  · iexact Hvs
  done
end proof

end bbolt
end EtcdGrove
end Perennial
