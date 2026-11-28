/-
Lean-first (no Rocq counterpart).

The proof of `pendEqual`: the lengths, then the loop's invariant is that the inputs before the index
are equal (`configEqual`'s loop).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.pendEqual
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.inputEqual

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_etcd3

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.k8s.etcd3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Assumptions]

theorem pendEqual.wp_proof (wp_inputEqual : inputEqual.spec (GF := GF) (hG := hG)) :
    pendEqual.spec (GF := GF) (hG := hG) := by
  intro a b xs ys
  wp_start as ⟨#Hap, #Hbp⟩
  ihave %Hla := ownSlice_len $$ Hap
  ihave %Hlb := ownSlice_len $$ Hbp
  wp_auto
  wp_if_destruct
  · have Heq := Hif; clear Hif
    rename_i iu_ptr
    irename : (iu_ptr ↦ zero_val w64 : IProp GF) => Hiu
    ihave HI : (∃ (i j : w64),
        "i" ∷ i_ptr ↦ i ∗ "Hiu" ∷ iu_ptr ↦ j ∗
        "%Hi" ∷ ⌜0 ≤ sint.Z i ∧ sint.Z i ≤ sint.Z a.len ∧
          xs.take (sint.nat i) = ys.take (sint.nat i)⌝ : IProp GF) $$ [i Hiu]
    · iexists W64 0, _
      iframe
      ipureintro; refine ⟨by word, by word, rfl⟩
    wp_for HI
    wp_if_destruct
    · have Hb' : 0 ≤ sint.Z i ∧ sint.Z i < sint.Z a.len := ⟨Hi.1, Hif⟩
      have Hb2' : 0 ≤ sint.Z i ∧ sint.Z i < sint.Z b.len := by rw [← Heq]; exact Hb'
      list_elem xs (sint.nat i) as w
      list_elem ys (sint.nat i) as w2
      simp only [Hb', _root_.and_self, ↓reduceIte]
      wp_apply wp_load_slice_index a (sint.Z i) xs _ w Hi.1 $$ [Hap] as -
      · isplit
        · iexact Hap
        · ipureintro; exact Hw_lookup
      simp only [Hb', _root_.and_self, ↓reduceIte]
      wp_apply wp_load_slice_index a (sint.Z i) xs _ w Hi.1 $$ [Hap] as -
      · isplit
        · iexact Hap
        · ipureintro; exact Hw_lookup
      simp only [Hb2', _root_.and_self, ↓reduceIte]
      wp_apply wp_load_slice_index b (sint.Z i) ys _ w2 Hi.1 $$ [Hbp] as -
      · isplit
        · iexact Hbp
        · ipureintro; exact Hw2_lookup
      wp_apply wp_inputEqual w w2
      wp_if_destruct
      · wp_for_post
        iframe
        iexists i + W64 1, _
        iframe
        ipureintro
        refine ⟨by word, by word, ?_⟩
        rw [show sint.nat (i + W64 1) = sint.nat i + 1 by word, List.take_add_one,
          List.take_add_one, Hi.2.2, Hw_lookup, Hw2_lookup, Hif]
      · have hne : xs ≠ ys := fun h => Hif (by
          subst h; rw [Hw_lookup] at Hw2_lookup; cases Hw2_lookup; rfl)
        wp_for_post
        rw [decide_eq_false hne]
        iapply HΦ; itrivial
    · have h1 : xs.length = sint.nat i := by word
      have h2 : ys.length = sint.nat i := by rw [Hlb.1, ← Heq]; word
      have heq : xs = ys := by
        have := Hi.2.2
        rwa [← h1, List.take_length, h1, ← h2, List.take_length] at this
      rw [decide_eq_true heq]
      iapply HΦ; itrivial
  · rw [decide_eq_false (fun h => Hif (by subst h; word))]
    iapply HΦ; itrivial

end proof

end k8s_etcd3
end EtcdGrove
end Perennial
