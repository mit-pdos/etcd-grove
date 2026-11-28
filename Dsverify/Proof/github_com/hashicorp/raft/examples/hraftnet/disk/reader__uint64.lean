/-
(hraft_robust R3) The proof of `disk.(*reader).uint64` (the accumulator as `etcd/wal`'s `decoder.u64`).
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.disk.reader__uint64

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.hashicorp.raft.examples.hraftnet.disk.Assumptions]

open github_com.hashicorp.raft.examples.hraftnet.disk

theorem rd_lt8 (i : w64) (h : uint.Z i < uint.Z (W64 8)) : uint.nat i < 8 := by word

theorem rd_eq8 (i : w64) (h : ¬ uint.Z i < uint.Z (W64 8)) (h' : uint.nat i ≤ 8) : uint.nat i = 8 := by word

theorem rd_idx (i len : w64) (n : Nat) (hi : uint.nat i < 8) (hn : 8 ≤ n)
    (hl : n = sint.nat len ∧ 0 ≤ sint.Z len) : 0 ≤ sint.Z i ∧ sint.Z i < sint.Z len := by
  obtain ⟨h1, h2⟩ := hl; constructor <;> word

theorem rd_toNat (i : w64) (hi : uint.nat i < 8) : (sint.Z i).toNat = uint.nat i := by word

theorem rd_mul (i : w64) (hi : uint.nat i < 8) : W64 8 * i = W64 8 * W64 ((uint.nat i : Nat) : Int) := by
  word

theorem rd_succ (i : w64) (hi : uint.nat i < 8) : uint.nat (i + W64 1) = uint.nat i + 1 := by word

theorem rd_len8 (len : w64) (n : Nat) (hn : 8 ≤ n) (hl : n = sint.nat len ∧ 0 ≤ sint.Z len) :
    ¬ sint.Z len < sint.Z (W64 8) := by
  obtain ⟨h1, h2⟩ := hl; word

theorem rd_le8 (len : w64) (n : Nat) (hn : 8 ≤ n) (hl : n = sint.nat len ∧ 0 ≤ sint.Z len) :
    sint.Z (W64 8) ≤ sint.Z len := by
  obtain ⟨h1, h2⟩ := hl; word

theorem github_com.hashicorp.raft.examples.hraftnet.disk.reader.uint64.wp_proof :
    github_com.hashicorp.raft.examples.hraftnet.disk.reader.uint64.spec (GF := GF) (hG := hG) := by
  intro r x rest
  wp_start as Hr
  iunfold readerSt at Hr
  icases Hr with ⟨%sl, Hr, #Hsl⟩
  ihave %Hlen := ownSlice_len $$ Hsl
  wp_auto
  have hl8 : 8 ≤ (encU64 x ++ rest).length := by simp [encU64_length]
  wp_if_destruct
  · exfalso; exact rd_len8 sl.len _ hl8 Hlen Hif
  ihave HI : (∃ (i : w64),
      "i" ∷ i_ptr ↦ i ∗ "x" ∷ x_ptr ↦ u64Acc x (uint.nat i) ∗
      "%Hi" ∷ ⌜uint.nat i ≤ 8⌝ : IProp GF) $$ [i x]
  · iexists W64 0
    rw [show uint.nat (W64 0) = 0 from rfl, u64Acc_zero]
    iframe
    ipureintro; omega
  wp_for HI
  wp_if_destruct
  · have hi8 : uint.nat i < 8 := rd_lt8 i Hif
    have hb : 0 ≤ sint.Z i ∧ sint.Z i < sint.Z sl.len := rd_idx i sl.len _ hi8 hl8 Hlen
    simp only [hb, _root_.and_self, ↓reduceIte]
    wp_apply wp_load_slice_index sl _ (encU64 x ++ rest) DFrac.discard _ hb.1 $$ [Hsl] as -
    · isplitl []
      · iexact Hsl
      · ipureintro
        rw [rd_toNat i hi8,
          List.getElem?_append_left (by rw [encU64_length]; exact hi8), encU64_getElem? x _ hi8]
    rw [rd_mul i hi8,
      show W64 (8 * ((uint.nat i : Nat) : Int)) = W64 (8 * ((uint.nat i : Nat) : Int)) from rfl,
      u64Acc_step' x (uint.nat i) hi8]
    wp_for_post
    iframe
    iexists i + W64 1
    rw [rd_succ i hi8]
    iframe
    ipureintro; omega
  · have hi8 : uint.nat i = 8 := rd_eq8 i Hif Hi
    rw [hi8, u64Acc_eight]
    ihave %Hwf := ownSlice_wf $$ Hsl
    have hb : 0 ≤ sint.Z (W64 8) ∧ sint.Z (W64 8) ≤ sint.Z sl.len ∧ sint.Z sl.len ≤ sint.Z sl.cap := by
      exact ⟨by decide, rd_le8 sl.len _ hl8 Hlen, Hwf.2⟩
    ihave Hrest := ownSlice_suffix_ro (W64 8) sl _ ⟨hb.1, hb.2.1⟩ $$ Hsl
    have hd : (encU64 x ++ rest).drop (sint.nat (W64 8)) = rest := by
      have h8 : sint.nat (W64 8) = (encU64 x).length := by rw [encU64_length]; decide
      rw [h8, List.drop_left]
    simp only [hb, _root_.and_self, ↓reduceIte]
    wp_auto
    iapply HΦ
    iunfold readerSt
    iexists _
    iframe Hr
    iapply (show (slice.slice sl w8 (W64 8) sl.len ↦*□ (encU64 x ++ rest).drop (sint.nat (W64 8)) : IProp GF) ⊢
      slice.slice sl w8 (W64 8) sl.len ↦*□ rest by rw [hd]) $$ Hrest

end proof

end Perennial
