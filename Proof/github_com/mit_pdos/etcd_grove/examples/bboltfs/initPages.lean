/- Lean-first (no Rocq counterpart). The proof of `initPages`: over the zeroed buffer's bytes, the two meta pages (the loop) and the freelist and leaf pages' headers, then the bytes are `initBytes`. -/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.bboltfs.initPages
public import Spec.github_com.mit_pdos.etcd_grove.examples.bboltfs.Page__meta
public import Spec.github_com.mit_pdos.etcd_grove.examples.bboltfs.Meta__sum64
public import Spec.github_com.mit_pdos.etcd_grove.examples.bboltfs.pageAt

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bboltfs

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode github_com.mit_pdos.etcd_grove.examples.bboltfs

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.bboltfs.Assumptions]

theorem initPages.wp_proof (wp_pageAt : pageAt.spec (GF := GF) (hG := hG))
    (wp_meta : Page.«meta».spec (GF := GF) (hG := hG))
    (wp_sum64 : Meta.sum64.spec (GF := GF) (hG := hG)) :
    initPages.spec (GF := GF) (hG := hG) := by
  intro buf
  wp_start as Hs
  generalize hIM : initMeta = IM
  ihave %Hlen := ownSlice_len $$ Hs
  ihave %Hpos := ownSlice_ptr_pos buf _ _ (by simp) $$ Hs
  icases ownSlice_bytes_acc go.uint8 (.scalar _ _ .isPlainScalar_uint8) buf _ _ Hpos $$ Hs
    with ⟨Hb, Hclose⟩
  simp only [flatMap_encode_w8]
  ihave %Hbd := bytesPointsto_in_bounds _ _ _ (by simp) $$ Hb
  have hmax : buf.ptr.addr + 16384 ≤ maxAddr := by
    have := Hbd.2; simp only [List.length_replicate] at this; exact this
  rw [zeroBytes_four]
  icases (fourPages_view _ _ _ _ _ _ (by simp) (by simp) (by simp)).1 $$ Hb with ⟨B0, B1, B2, B3⟩
  have hp : ∀ k : Nat, 0 < (buf.ptr +ₗ ((4096 * k : Nat) : Int)).addr := by
    intro k; simp only [Loc.add]; omega
  icases (zeroPage_meta_view _ _ (hp 0)).1 $$ B0 with ⟨H0, M0, R0⟩
  icases (zeroPage_meta_view _ _ (hp 1)).1 $$ B1 with ⟨H1, M1, R1⟩
  icases (zeroPage_hdr_view _ _ (hp 2)).1 $$ B2 with ⟨H2, R2⟩
  icases (zeroPage_hdr_view _ _ (hp 3)).1 $$ B3 with ⟨H3, R3⟩
  ihave S0 : metaSlot IM buf.ptr 0 (decide (0 < 0)) $$ [H0 M0]
  · rw [show decide (0 < 0) = false from rfl]
    iapply (metaSlot_false _ _ _).2; iframe
  ihave S1 : metaSlot IM buf.ptr 1 (decide (1 < 0)) $$ [H1 M1]
  · rw [show decide (1 < 0) = false from rfl]
    iapply (metaSlot_false _ _ _).2; iframe
  wp_auto
  ihave HI : (∃ (j : w64), "i" ∷ i_ptr ↦ j ∗
      "S0" ∷ metaSlot IM buf.ptr 0 (decide (0 < sint.nat j)) ∗
      "S1" ∷ metaSlot IM buf.ptr 1 (decide (1 < sint.nat j)) ∗
      "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ 2⌝ : IProp GF) $$ [i S0 S1]
  · iexists W64 0; iframe; ipureintro; decide
  wp_for HI
  wp_if_destruct
  · rw [show sint.Z (W64 2) = 2 from rfl] at Hif
    have hn : sint.nat j < 2 := by show (sint.Z j).toNat < 2; omega
    have hjn : ((sint.nat j : Nat) : Int) = sint.Z j := by
      show (((sint.Z j).toNat : Nat) : Int) = sint.Z j; omega
    ihave HS := metaSlots_open IM buf.ptr (sint.nat j) hn $$ [S0 S1]
    · iframe
    icases HS with ⟨Sn, So⟩
    icases (metaSlot_false _ _ _).1 $$ Sn with ⟨Hn, Mn⟩
    have hlen : sint.Z buf.len = 16384 := by
      have h : 16384 = sint.nat buf.len := by rw [← Hlen.1, List.length_replicate]; (try rfl)
      have : sint.nat buf.len = (sint.Z buf.len).toNat := rfl
      have := Hlen.2
      omega
    have haddr : sint.Z (j * W64 4096) = ((4096 * sint.nat j : Nat) : Int) := by
      have e : ((4096 * sint.nat j : Nat) : Int) = 4096 * sint.Z j := by omega
      rw [e]; word
    (try wp_auto)
    wp_apply wp_pageAt
    · ipureintro; rw [haddr, hlen]; omega
    rw [haddr]
    have hln : (buf.ptr +ₗ ((4096 * sint.nat j : Nat) : Int)) ≠ null := by
      have := hp (sint.nat j); intro h; rw [h] at this; simp [null] at this
    icases typedPointsto_split _ _ _ $$ Hn with Hn
    simp only [TypedPointsto.typedPointstoDef]
    icases Hn with ⟨Hid, Hflags, Hcount, Hoverflow, -⟩
    (try wp_auto)
    wp_apply wp_meta
    · ipureintro; simp only [Loc.add]; omega
    icases typedPointsto_split _ _ _ $$ Mn with Mn
    simp only [TypedPointsto.typedPointstoDef]
    icases Mn with ⟨Hmagic, Hversion, HpageSize, Hmflags, Hroot, Hfreelist, Hpgid, Htxid, Hchecksum, -⟩
    simp only [github_com.mit_pdos.etcd_grove.examples.bboltfs.magic,
      github_com.mit_pdos.etcd_grove.examples.bboltfs.version]
    (try wp_auto)
    have hjW : W64 ((sint.nat j : Nat) : Int) = j := by rw [hjn]; exact BitVec.ofInt_toInt
    have hmn : (buf.ptr +ₗ ((4096 * sint.nat j : Nat) : Int) +ₗ 16) ≠ null := by
      intro h; have := hp (sint.nat j); simp only [Loc.add, null] at h this ⊢
      have := congrArg Loc.addr h; simp at this; omega
    rw [show sint.Z (W64 4096) = 4096 from rfl]
    ihave Mn : (buf.ptr +ₗ ((4096 * sint.nat j : Nat) : Int) +ₗ 16) ↦ initMeta0 (sint.nat j) $$
      [Hmagic Hversion HpageSize Hmflags Hroot Hfreelist Hpgid Htxid Hchecksum]
    · iapply typedPointsto_combine _ _ _ hmn
      simp only [TypedPointsto.typedPointstoDef, initMeta0, hjW, zeroMeta]
      iframe
    have hmpos : 0 < (buf.ptr +ₗ ((4096 * sint.nat j : Nat) : Int) +ₗ 16).addr := by
      have := hp (sint.nat j); simp only [Loc.add] at this ⊢; omega
    wp_apply wp_sum64 _ _ (DFrac.own 1) $$ [Mn] as Mn
    · iframe Mn; ipureintro; exact hmpos
    icases typedPointsto_split _ _ _ $$ Mn with Mn
    simp only [TypedPointsto.typedPointstoDef]
    icases Mn with ⟨Hmagic, Hversion, HpageSize, Hmflags, Hroot, Hfreelist, Hpgid, Htxid, Hchecksum, -⟩
    (try wp_auto)
    ihave Mn : (buf.ptr +ₗ ((4096 * sint.nat j : Nat) : Int) +ₗ 16) ↦ IM (sint.nat j) $$
      [Hmagic Hversion HpageSize Hmflags Hroot Hfreelist Hpgid Htxid Hchecksum]
    · iapply typedPointsto_combine _ _ _ hmn
      rw [← hIM]
      simp only [TypedPointsto.typedPointstoDef, initMeta]
      iframe
    ihave Hn : (buf.ptr +ₗ ((4096 * sint.nat j : Nat) : Int)) ↦ pageHdr (W64 ((sint.nat j : Nat) : Int)) (W16 4) $$
      [Hid Hflags Hcount Hoverflow]
    · iapply typedPointsto_combine _ _ _ hln
      simp only [TypedPointsto.typedPointstoDef, pageHdr, hjW]
      iframe
    ihave Sn := (metaSlot_true IM buf.ptr (sint.nat j)).2 $$ [Hn Mn]
    · iframe
    ihave HS := metaSlots_close IM buf.ptr (sint.nat j) hn $$ [Sn So]
    · iframe
    icases HS with ⟨S0, S1⟩
    have hj1 : sint.nat (j + W64 1) = sint.nat j + 1 := by
      show (sint.Z (j + W64 1)).toNat = (sint.Z j).toNat + 1
      have : sint.Z (j + W64 1) = sint.Z j + 1 := by word
      omega
    wp_for_post
    ihave HI : (∃ (j : w64), "i" ∷ i_ptr ↦ j ∗
        "S0" ∷ metaSlot IM buf.ptr 0 (decide (0 < sint.nat j)) ∗
        "S1" ∷ metaSlot IM buf.ptr 1 (decide (1 < sint.nat j)) ∗
        "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ 2⌝ : IProp GF) $$ [i S0 S1]
    · iexists (j + W64 1)
      rw [hj1]
      iframe
      ipureintro; constructor <;> word
    iframe
  · rw [show sint.Z (W64 2) = 2 from rfl] at Hif
    have hj2 : sint.nat j = 2 := by show (sint.Z j).toNat = 2; omega
    rw [hj2, show decide (0 < 2) = true from rfl, show decide (1 < 2) = true from rfl]
    subst hIM
    icases (metaSlot_true _ _ _).1 $$ S0 with ⟨H0, M0⟩
    icases (metaSlot_true _ _ _).1 $$ S1 with ⟨H1, M1⟩
    have hlen : sint.Z buf.len = 16384 := by
      have h : 16384 = sint.nat buf.len := by rw [← Hlen.1, List.length_replicate]; (try rfl)
      have : sint.nat buf.len = (sint.Z buf.len).toNat := rfl
      have := Hlen.2
      omega
    (try wp_auto)
    wp_apply wp_pageAt
    · ipureintro; rw [hlen]; exact ⟨Hpos, by decide, by decide⟩
    rw [show sint.Z (W64 2 * W64 4096) = ((4096 * 2 : Nat) : Int) from rfl]
    have hn2 : (buf.ptr +ₗ ((4096 * 2 : Nat) : Int)) ≠ null := by
      have := hp 2; intro h; rw [h] at this; simp [null] at this
    icases typedPointsto_split _ _ _ $$ H2 with H2
    simp only [TypedPointsto.typedPointstoDef]
    icases H2 with ⟨Hid, Hflags, Hcount, Hoverflow, -⟩
    (try wp_auto)
    ihave H2 : (buf.ptr +ₗ ((4096 * 2 : Nat) : Int)) ↦ pageHdr (W64 2) (W16 16) $$
      [Hid Hflags Hcount Hoverflow]
    · iapply typedPointsto_combine _ _ _ hn2
      simp only [TypedPointsto.typedPointstoDef, pageHdr]
      iframe
    wp_apply wp_pageAt
    · ipureintro; rw [hlen]; exact ⟨Hpos, by decide, by decide⟩
    rw [show sint.Z (W64 3 * W64 4096) = ((4096 * 3 : Nat) : Int) from rfl]
    have hn3 : (buf.ptr +ₗ ((4096 * 3 : Nat) : Int)) ≠ null := by
      have := hp 3; intro h; rw [h] at this; simp [null] at this
    icases typedPointsto_split _ _ _ $$ H3 with H3
    simp only [TypedPointsto.typedPointstoDef]
    icases H3 with ⟨Hid, Hflags, Hcount, Hoverflow, -⟩
    (try wp_auto)
    ihave H3 : (buf.ptr +ₗ ((4096 * 3 : Nat) : Int)) ↦ pageHdr (W64 3) (W16 2) $$
      [Hid Hflags Hcount Hoverflow]
    · iapply typedPointsto_combine _ _ _ hn3
      simp only [TypedPointsto.typedPointstoDef, pageHdr]
      iframe
    ihave B0 := (metaPage_view _ _ 0 (hp 0)).2 $$ [H0 M0 R0]
    · iframe
    ihave B1 := (metaPage_view _ _ 1 (hp 1)).2 $$ [H1 M1 R1]
    · iframe
    ihave B2 := (emptyPage_view _ _ (W64 2) (W16 16) (hp 2)).2 $$ [H2 R2]
    · iframe
    ihave B3 := (emptyPage_view _ _ (W64 3) (W16 2) (hp 3)).2 $$ [H3 R3]
    · iframe
    ihave Hb : bytesPointsto buf.ptr (DFrac.own 1) initBytes $$ [B0 B1 B2 B3]
    · unfold initBytes
      iapply (fourPages_view buf.ptr _ _ _ _ _ (metaPageBytes_length 0) (metaPageBytes_length 1)
        (emptyPageBytes_length _ _)).2
      iframe
    ihave Hs := Hclose $$ %initBytes [] [Hb]
    · ipureintro
      simp only [initBytes_length, List.length_append, List.length_replicate]
      rfl
    · iexact Hb
    iapply HΦ $$ Hs

end proof

end bboltfs
end EtcdGrove
end Perennial
