/- Lean-first (no Rocq counterpart).

`b.equal(b2)`: the lengths, then a loop over the words.
-/
module

public import Spec.github_com.anishathalye.porcupine.bitset__equal

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace porcupine

open Iris Iris.BI Iris.ProofMode github_com.anishathalye.porcupine

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.anishathalye.porcupine.Assumptions]

theorem bitset.equal.wp_proof : bitset.equal.spec (GF := GF) (hG := hG) :=
    fun b ws dq b2 ws2 dq2 => by
  wp_start as ⟨Hb, Hb2⟩
  ihave %Hlen := ownSlice_len $$ Hb
  ihave %Hlen2 := ownSlice_len $$ Hb2
  wp_auto
  wp_if_destruct
  · rename_i iu_ptr
    have Heq := Hif; clear Hif
    irename : (iu_ptr ↦ zero_val w64 : IProp GF) => Hiu
    ihave HI : (∃ (i j : w64),
        "i" ∷ i_ptr ↦ i ∗ "Hiu" ∷ iu_ptr ↦ j ∗
        "%Hi" ∷ ⌜0 ≤ sint.Z i ∧ sint.Z i ≤ sint.Z b.len ∧
          ws.take (sint.nat i) = ws2.take (sint.nat i)⌝ : IProp GF) $$ [i Hiu]
    · iexists W64 0, _
      iframe
      ipureintro; refine ⟨by word, by word, rfl⟩
    wp_for HI
    wp_if_destruct
    · have Hb' : 0 ≤ sint.Z i ∧ sint.Z i < sint.Z b.len := ⟨Hi.1, Hif⟩
      have Hb2' : 0 ≤ sint.Z i ∧ sint.Z i < sint.Z b2.len := by rw [← Heq]; exact Hb'
      simp only [Hb', _root_.and_self, ↓reduceIte]
      list_elem ws (sint.nat i) as w
      list_elem ws2 (sint.nat i) as w2
      wp_apply wp_load_slice_index b (sint.Z i) ws dq w Hi.1 $$ [Hb] as Hb
      · iframe; ipureintro; exact Hw_lookup
      simp only [Hb', _root_.and_self, ↓reduceIte]
      wp_apply wp_load_slice_index b (sint.Z i) ws dq w Hi.1 $$ [Hb] as Hb
      · iframe; ipureintro; exact Hw_lookup
      simp only [Hb2', _root_.and_self, ↓reduceIte]
      wp_apply wp_load_slice_index b2 (sint.Z i) ws2 dq2 w2 Hi.1 $$ [Hb2] as Hb2
      · iframe; ipureintro; exact Hw2_lookup
      wp_if_destruct
      · wp_for_post
        iframe
        iexists i + W64 1, _
        iframe
        ipureintro
        refine ⟨by word, by word, ?_⟩
        rw [show sint.nat (i + W64 1) = sint.nat i + 1 by word, List.take_add_one, List.take_add_one,
          Hi.2.2, Hw_lookup, Hw2_lookup, ‹w = w2›]
      · wp_for_post
        have hne : ws ≠ ws2 := fun h => ‹¬ w = w2› (by subst h; rw [Hw_lookup] at Hw2_lookup; cases Hw2_lookup; rfl)
        rw [show decide (ws = ws2) = false from decide_eq_false hne]
        iapply HΦ
        iframe
    · have h1 : ws.length = sint.nat i := by word
      have h2 : ws2.length = sint.nat i := by rw [Hlen2.1, ← Heq]; word
      have heq : ws = ws2 := by
        have := Hi.2.2
        rwa [← h1, List.take_length, h1, ← h2, List.take_length] at this
      rw [show decide (ws = ws2) = true from decide_eq_true heq]
      iapply HΦ
      iframe
  · have hne : ws ≠ ws2 := fun h => Hif (by subst h; word)
    rw [show decide (ws = ws2) = false from decide_eq_false hne]
    iapply HΦ
    iframe

end proof

end porcupine
end EtcdGrove
end Perennial
