/-
The definitions, specs and lemmas of `PutVarint.lean` that its proofs do not need (split out for the import tiers, CLAUDE.md "Import tiers": its importers that are not linking modules import this module, and see no proof).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.MarshalSpecs
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.client.VarintPure

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

theorem swift.uvarint_ge (m : Nat) (h : 128 ≤ m) :
    sp.uvarint m = W8 ((m % 128 + 128 : Nat) : Int) :: sp.uvarint (m / 128) := by
  rw [sp.uvarint, dite_eq_right (by omega)]; rfl

theorem swift.uvarint_lt (m : Nat) (h : m < 128) : sp.uvarint m = [W8 (m : Int)] := by
  rw [sp.uvarint, dite_eq_left h]

theorem swift.uvarint_len_pos (m : Nat) : 1 ≤ (sp.uvarint m).length := by
  rw [sp.uvarint]; split <;> simp

theorem swift.set_front {A : Type} (pre bs : List A) (v : A) (h : pre.length < bs.length) :
    (pre ++ bs.drop pre.length).set pre.length v = pre ++ v :: bs.drop (pre.length + 1) := by
  rw [List.set_append_right _ _ (by omega), Nat.sub_self]
  congr 1
  obtain ⟨b, rest, hb⟩ : ∃ b rest, bs.drop pre.length = b :: rest := by
    cases hd : bs.drop pre.length with
    | nil => simp at hd; omega
    | cons b rest => exact ⟨b, rest, rfl⟩
  rw [hb]
  have : bs.drop (pre.length + 1) = rest := by
    rw [← List.drop_drop, hb]; rfl
  rw [this]; rfl

theorem swift.shr7 (m : Nat) (h : m < 2 ^ 64) :
    W64 (m : Int) >>> W64 7 = W64 ((m / 128 : Nat) : Int) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.ushiftRight_eq', BitVec.toNat_ushiftRight]
  have h1 : (W64 (m : Int)).toNat = m := by simp [W64]; omega
  have h2 : (W64 7).toNat = 7 := rfl
  have h3 : (W64 ((m / 128 : Nat) : Int)).toNat = m / 128 := by simp [W64]; omega
  rw [h1, h2, h3, Nat.shiftRight_eq_div_pow]

theorem swift.or128_all : ∀ x : BitVec 8, x ||| 128 = BitVec.ofNat 8 (x.toNat % 128 + 128) := by
  decide

theorem swift.uintZ_W64 (m : Nat) (h : m < 2 ^ 64) : uint.Z (W64 (m : Int)) = m := by
  simp only [uint.Z, W64]; rw [BitVec.toNat_ofInt]; omega

theorem swift.byte_or (m : Nat) (h : m < 2 ^ 64) :
    (W8 (uint.Z (W64 (m : Int))) ||| W8 128) = W8 ((m % 128 + 128 : Nat) : Int) := by
  rw [swift.uintZ_W64 m h, show W8 128 = (128 : BitVec 8) from rfl, swift.or128_all]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat, W8, BitVec.toNat_ofInt]
  omega

section proofs
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF]
variable [swift.Assumptions]

set_option goose.wp.extras true

theorem swift.wp_putUvarint (s : GoSlice) (bs : List w8) (n : Nat) :
    {{ (s ↦* bs : IProp netDistGF) ∗ ⌜n < 2 ^ 64 ∧ (sp.uvarint n).length ≤ bs.length⌝ }}
      (App (App (Val (@! swift.putUvarint)) (Val #s)) (Val #(W64 (n : Int))))
    {{ (r : w64), RET #r;
        ⌜sint.Z r = ((sp.uvarint n).length : Int)⌝ ∗
        s ↦* (sp.uvarint n ++ bs.drop (sp.uvarint n).length) }} := by
  wp_start as ⟨Hs, %Hn⟩
  obtain ⟨hn64, hlen⟩ := Hn
  have hl10 : (sp.uvarint n).length ≤ 10 := sp.uvarint_length n 10 (by decide) (by omega)
  wp_auto
  ihave HL : (∃ (pre : List w8) (m : Nat),
      "i" ∷ i_ptr ↦ W64 (pre.length : Int) ∗ "x" ∷ x_ptr ↦ W64 (m : Int) ∗
      "Hs" ∷ s ↦* (pre ++ bs.drop pre.length) ∗
      "%Hpre" ∷ ⌜sp.uvarint n = pre ++ sp.uvarint m ∧ m < 2 ^ 64⌝ : IProp netDistGF)
    $$ [i x Hs]
  · iexists [], n
    simp only [List.length_nil, List.drop_zero, List.nil_append]
    iframe
    ipureintro; exact ⟨by simp, hn64⟩
  wp_for HL
  obtain ⟨hpre, hm⟩ := Hpre
  have hpl : pre.length + (sp.uvarint m).length = (sp.uvarint n).length := by
    rw [hpre, List.length_append]
  have hm1 := swift.uvarint_len_pos m
  have hk : pre.length < bs.length := by omega
  have hk10 : pre.length < 10 := by omega
  have hz : sint.Z (W64 (pre.length : Int)) = (pre.length : Int) := by
    word
  have hlenS : ((pre ++ bs.drop pre.length).length : Int) = bs.length := by
    simp only [List.length_append, List.length_drop]; omega
  ihave %Hsl := ownSlice_len $$ Hs
  have hsl : sint.Z s.len = bs.length := by
    have h1 := Hsl.1; have h2 := Hsl.2
    simp only [List.length_append, List.length_drop] at h1
    have h3 : ((sint.nat s.len : Nat) : Int) = sint.Z s.len := Int.toNat_of_nonneg h2
    omega
  wp_if_destruct
  · have hge : 128 ≤ m := by
      rename_i Hif
      revert Hif; rw [swift.uintZ_W64 m hm]; intro Hif; exact_mod_cast (by simpa using Hif)
    rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by rw [hz]; omega, by rw [hz]; omega⟩)]
    wp_apply wp_store_slice_index _ _ _ _ $$ [Hs] as Hs
    · iframe Hs; ipureintro
      rw [hz]; omega
    wp_for_post
    iframe
    iexists pre ++ [W8 ((m % 128 + 128 : Nat) : Int)], m / 128
    have hu := swift.uvarint_ge m hge
    rw [swift.byte_or m hm, swift.shr7 m hm, hz, Int.toNat_natCast, swift.set_front _ _ _ hk]
    rw [show W64 (pre.length : Int) + W64 1 = W64 ((pre ++ [W8 ((m % 128 + 128 : Nat) : Int)]).length : Int)
      by simp only [List.length_append, List.length_singleton]; word]
    simp only [List.length_append, List.length_singleton, List.append_assoc, List.singleton_append]
    iframe
    ipureintro
    refine ⟨?_, by omega⟩
    rw [hpre, hu]
  · have hlt : m < 128 := by
      rename_i Hif
      revert Hif; rw [swift.uintZ_W64 m hm]; intro Hif; exact_mod_cast (by simpa using Hif)
    have hu := swift.uvarint_lt m hlt
    rw [hu] at hpre
    rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by rw [hz]; omega, by rw [hz]; omega⟩)]
    wp_apply wp_store_slice_index _ _ _ _ $$ [Hs] as Hs
    · iframe Hs; ipureintro
      rw [hz]; omega
    wp_auto
    iapply HΦ
    rw [swift.uintZ_W64 m hm, hz, Int.toNat_natCast, swift.set_front _ _ _ hk, hpre]
    simp only [List.length_append, List.length_singleton, List.append_assoc, List.singleton_append]
    iframe
    ipureintro
    word

end proofs

end Perennial.github_com.imdea_software.swiftpaxos
