/-
`typed.mergingWalker.derefList`: proved (Prove phase, 2026-11-19): nil for an absent side, else
`listValue`'s view (no error: the side is `null` or a list, the premise).
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.mergingWalker__derefList
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.listValue
public import Proof.sigs_k8s_io.structured_merge_diff.v7.typed.LawProofsBPers

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

theorem typed.mergingWalker.derefList.wp_proof
    (h_listValue : typed.listValue.spec (GF := GF)) :
    typed.mergingWalker.derefList.spec (GF := GF) := fun w wv dqw pfx v dq o => by
  wp_start as ⟨Hw, Hv, %Ho⟩
  wp_auto
  rcases o with _ | x
  · ihave ⟨Hv, %Hvn⟩ := isValO_nil $$ Hv
    rw [Hvn.2 rfl]
    wp_auto
    iapply HΦ
    iframe
    isplitr
    · unfold isListO listOfO; ipureintro; rfl
    · iapply errsIff_nil; simp
  · ihave ⟨Hv, %Hvp⟩ := isValO_some $$ Hv
    obtain ⟨p, Hp⟩ := Hvp
    rw [Hp]
    wp_auto
    ihave ⟨Hw, %Hnn⟩ := typedPointsto_not_null_dup _ _ _ $$ Hw
    iStructNamed Hw
    wp_auto
    have Hok : some x = some UVal.null ∨ (listOfO (some x)).isSome = true := by
      rcases Ho with h | h | h
      · cases h
      · exact Or.inl h
      · exact Or.inr h
    have Hok' : x = UVal.null ∨ (listOfO (some x)).isSome = true := by
      rcases Hok with h | h
      · exact Or.inl (Option.some.inj h)
      · exact Or.inr h
    simp only [isValO]
    wp_apply h_listValue wv.allocator' _ dq x $$ [Hv] as %m %err ⟨Hv, Hm, %Herr⟩
    · iexact Hv
    rw [Herr.2 Hok']
    wp_auto
    iapply HΦ
    iframe
    isplitl
    · iapply typedPointsto_combine _ _ _ Hnn
      simp only [TypedPointsto.typedPointstoDef]
      iframe
    · iapply errsIff_nil; exact Or.inr Hok


end proof

end smd
end EtcdGrove
end Perennial
