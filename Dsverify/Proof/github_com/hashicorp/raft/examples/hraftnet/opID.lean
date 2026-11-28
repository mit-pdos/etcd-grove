/-
`hraftnet.opID`'s proof: the loop stores `x`'s bytes, big-endian, into a fresh 8-byte slice.
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.opID

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace github_com.hashicorp.raft.examples.hraftnet

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : Assumptions]

set_option goose.wp.extras true

/-- Storing the next byte of `l1` over `l2` (rabia's `CodecProof.lean`). -/
theorem take_drop_set' {l1 l2 : List w8} {n : Nat} {a : w8} (h1 : l1[n]? = some a)
    (h2 : n < l2.length) :
    (l1.take n ++ l2.drop n).set n a = l1.take (n + 1) ++ l2.drop (n + 1) := by
  have hn : n < l1.length := by
    rcases Nat.lt_or_ge n l1.length with h | h
    · exact h
    · rw [List.getElem?_eq_none h] at h1; cases h1
  have ht : (l1.take n).length = n := by simp; omega
  rw [List.set_append, ite_eq_right (by omega), ht, Nat.sub_self, List.take_add_one, h1]
  rw [List.drop_eq_getElem_cons h2, List.set_cons_zero]
  simp

theorem opID.wp_proof : opID.spec (GF := GF) := by
  intro c s
  wp_start as -
  wp_auto
  rw [show (c <<< W64 56 ||| s % W64 72057594037927936) = opIDW c s from rfl]
  wp_apply (wp_slice_make2 (V := w8) (W64 8)) as %b ⟨Hb, Hcap⟩
  · ipureintro; decide
  (try wp_auto)
  ihave %Hbl := ownSlice_len _ _ _ $$ Hb
  have hb8 : sint.Z b.len = 8 := by
    have := Hbl.1; simp only [List.length_replicate] at this; word
  ihave HI : (∃ (j : w64), "i" ∷ i_ptr ↦ j ∗
      "Hb" ∷ b ↦* ((beBytes (opIDW c s)).take (uint.nat j) ++ (List.replicate 8 (zero_val w8)).drop (uint.nat j)) ∗
      "%Hj" ∷ ⌜uint.nat j ≤ 8⌝ : IProp GF) $$ [i Hb]
  · iexists W64 0
    iframe
    ipureintro; simp
  wp_for HI
  wp_if_destruct
  · have hj8 : uint.nat j < 8 := by word
    have hj0 : 0 ≤ sint.Z j := by word
    have hjz : sint.Z j < 8 := by word
    have hs : 0 ≤ sint.Z j ∧ sint.Z j < sint.Z b.len := ⟨hj0, by omega⟩
    rw [ite_eq_left hs]
    wp_apply wp_store_slice_index b (sint.Z j) _ (W8 (uint.Z (opIDW c s >>> (W64 56 - W64 8 * j))))
      $$ [Hb] as Hb
    · have hlen : ((beBytes (opIDW c s)).take (uint.nat j) ++
          (List.replicate 8 (zero_val w8)).drop (uint.nat j)).length = 8 := by
        simp only [List.length_append, List.length_take, List.length_drop, beBytes_length,
          List.length_replicate]
        omega
      iframe Hb; ipureintro; rw [hlen]; exact ⟨hs.1, by exact_mod_cast hjz⟩
    wp_for_post
    iframe
    iexists j + W64 1
    have hsn : (sint.Z j).toNat = uint.nat j := by word
    rw [hsn, take_drop_set' (beBytes_getElem (opIDW c s) j hj8) (by simp; word),
      show uint.nat (j + W64 1) = uint.nat j + 1 by word]
    iframe
    ipureintro; word
  · have hj8 : uint.nat j = 8 := by word
    rw [hj8, List.take_of_length_le (by simp [beBytes_length]), List.drop_of_length_le (by simp),
      List.append_nil]
    iapply HΦ
    unfold opIDB
    iframe Hb Hcap

end proof

end github_com.hashicorp.raft.examples.hraftnet

end Perennial
