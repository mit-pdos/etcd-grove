/-
`typed.ValidationErrors.WithLazyPrefix`: not proved yet (`sorry`): the stage's Prove step, after the freeze
(notes/smd-plan.md). Draft (2026-11-19).
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.ValidationErrors__WithLazyPrefix

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace smd

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open sigs_k8s_io.structured_merge_diff.v7

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : typed.Assumptions]

theorem typed.ValidationErrors.WithLazyPrefix.wp_proof :
    typed.ValidationErrors.WithLazyPrefix.spec (GF := GF) := fun errs es f => by
  wp_start as ⟨Hs, Hf⟩
  ihave %Hlen := ownSlice_len $$ Hs
  wp_auto
  wp_if_destruct
  · iapply HΦ
    iexists es; iframe Hs; ipureintro; rfl
  have Hne : es ≠ [] := by
    intro h; subst h; apply Hif; simp at Hlen; word
  icases Hf with (%Hf | Hf)
  · exact absurd Hf Hne
  wp_if_destruct
  iclear Hf
  rotate_left
  iunfold prefixOk at Hf
  icases Hf with (%Hf | #Hf)
  exact absurd Hf Hif
  wp_apply Hf as %s %_
  iclear Hf
  all_goals
    rename_i igo
    irename : (igo ↦ zero_val w64 : IProp GF) => Higo
    irename «prefix» => Hpfx
    ihave IH : iprop(∃ (n k : w64) (ls : List typed.ValidationError),
        "i" ∷ i_ptr ↦ n ∗
        "Higo" ∷ igo ↦ k ∗
        "Hs" ∷ errs ↦* ls ∗
        "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ ls.length = es.length⌝) $$ [i Higo Hs]
    · iexists W64 0, _, es
      iframe i Higo Hs
      ipureintro; exact ⟨by word, rfl⟩
    wp_for IH
    wp_if_destruct
    · have Hbnd : 0 ≤ sint.Z n ∧ sint.Z n < sint.Z errs.len := ⟨Hn.1, Hif⟩
      have Hlt : (sint.Z n).toNat < ls.length := by rw [Hn.2]; word
      simp only [Hbnd, and_self, ↓reduceIte]
      obtain ⟨e, He⟩ : ∃ e, ls[(sint.Z n).toNat]? = some e := ⟨_, List.getElem?_eq_getElem Hlt⟩
      icases ownSlice_elem_acc (sint.Z n) e errs _ _ Hn.1 He $$ Hs with ⟨He, Hs⟩
      wp_auto
      simp only [Hbnd, and_self, ↓reduceIte]
      wp_auto
      simp only [Hbnd, and_self, ↓reduceIte]
      wp_auto
      ihave Hs := Hs $$ He
      wp_for_post
      iframe
      iexists n + W64 1, n, _
      iframe i Higo Hs
      ipureintro; exact ⟨by word, by rw [List.length_set]; exact Hn.2⟩
    · iapply HΦ
      iexists ls; iframe Hs; ipureintro; exact Hn.2

end proof

end smd
end EtcdGrove
end Perennial
