/-
The proof of `ConditionsMap.AllowConditions.spec`
(`Spec/k8s_io/apiserver/pkg/authorization/authorizer/ConditionsMap__AllowConditions.lean`).
Lean-first (no Rocq counterpart).
-/
module

public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.ConditionsMap__AllowConditions

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace authorizer

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode k8s_io.apiserver.pkg.authorization.authorizer

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.apiserver.pkg.authorization.authorizer.Assumptions]

theorem ConditionsMap.AllowConditions.wp_proof :
    ConditionsMap.AllowConditions.spec (GF := GF) (hG := hG) := by
  intro c cs
  wp_start as #Hcs
  iapply wp_fupd
  wp_auto
  ipersist c
  imodintro
  iapply HΦ
  unfold seqOk iterRunOk yield1Ok
  iintro !> %y %I %D #Hy
  wp_start as HI
  ihave #Hc := typedPointsto_split _ _ _ $$ c
  simp only [TypedPointsto.typedPointstoDef]
  iNamed Hc
  ihave %Hlen := ownSlice_len _ _ _ $$ Hcs
  wp_auto
  ihave HInv : (∃ (j : w64) (cv : GoInterface), "i" ∷ i_ptr ↦ j ∗ "cond" ∷ cond_ptr ↦ cv ∗
      "yield" ∷ yield_ptr ↦ y ∗ "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ sint.Z c.allowConditions'.len⌝ ∗
      "HI" ∷ I (sint.nat j) : IProp GF) $$ [i cond yield HI]
  · iexists W64 0, _
    iframe
    ipureintro; constructor <;> word
  wp_for HInv
  by_cases hlt : sint.Z j < sint.Z c.allowConditions'.len
  · simp only [hlt, _root_.decide_true, ↓reduceIte]
    wp_auto
    have hjl : sint.nat j < cs.length := by word
    obtain ⟨v, hv⟩ : ∃ v, cs[sint.nat j]? = some v := ⟨_, List.getElem?_eq_getElem hjl⟩
    have hb : 0 ≤ sint.Z j ∧ sint.Z j < sint.Z c.allowConditions'.len := ⟨Hj.1, hlt⟩
    simp only [hb, _root_.and_self, ↓reduceIte]
    wp_apply (wp_load_slice_index c.allowConditions' (sint.Z j) cs _ v Hj.1) $$ [] as -
    · iframe #; ipureintro; simpa [sint.nat] using hv
    wp_bind (App (Val #y) _)
    ihave #Hyj := Hy $$ %(sint.nat j) %v %hv
    iapply Hyj $$ HI
    iintro !> %b Hb
    cases b <;> simp only [Bool.false_eq_true, ↓reduceIte]
    · wp_auto
      wp_for_post
      iapply HΦ
      iright
      iexact Hb
    · wp_auto
      wp_for_post
      iframe
      iexists j + W64 1, v
      iframe
      have : sint.nat (j + W64 1) = sint.nat j + 1 := by word
      rw [this]
      iframe
      ipureintro; constructor <;> word
  · simp only [hlt, _root_.decide_false, Bool.false_eq_true, ↓reduceIte]
    wp_auto
    iapply HΦ
    ileft
    have : sint.nat j = cs.length := by word
    rw [this]
    iexact HI

end proof

end authorizer
end EtcdGrove
end Perennial
