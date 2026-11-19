/-
Lean-first (no Rocq counterpart).

Lemmas for the proofs of the union builder (`conditionsunion.go`: `Add`, `ToDecision`,
`collectReasonsAndErrors`): slices at a common fraction (`slices.Concat` takes its slices at one
fraction, and `collectReasonsAndErrors` concatenates its caller's prefix, at any fraction, with a
fresh literal), and pure facts about the model.
-/
module

public import Proof.k8s_io.apiserver.pkg.authorization.authorizer.Defs

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace authorizer

open Iris Iris.BI Iris.ProofMode k8s_io.apiserver.pkg.authorization.authorizer

section slices
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- An empty slice holds at any fraction. -/
theorem ownSlice_nil_frac {V : Type} [ZeroVal V] [TypedPointsto (GF := GF) V] (s : GoSlice)
    (dq dq' : DFrac) : (s ↦*{dq} ([] : List V) : IProp GF) ⊢ s ↦*{dq'} ([] : List V) := by
  rw [ownSlice_unseal]; unfold ownSliceDef
  iintro (%H | ⟨H, %Hc⟩)
  · ileft; ipureintro; exact H
  · icases typedPointsto_not_null _ _ _ $$ H with %Hnn
    icases array_len _ _ _ _ $$ H with %Hlen
    iright
    isplitl []
    · have Hlen' : sint.Z s.len = 0 := by simpa using Hlen
      rw [Hlen']
      iapply array_empty _ _ Hnn
    · ipureintro; exact Hc

/-- A non-empty slice of strings is owned at a valid fraction. -/
theorem ownSlice_string_valid' (s : GoSlice) (dq : DFrac) (x : GoString) (xs : List GoString) :
    (s ↦*{dq} (x :: xs) : IProp GF) ⊢ ⌜✓ dq⌝ := by
  have hx : typedPointsto (GF := GF) (arrayIndexRef GoString 0 s.ptr) x dq ⊢ ⌜✓ dq⌝ :=
    (typedPointsto_split _ _ _).trans (heapPointsto_valid _ _ _)
  rw [ownSlice_unseal]; unfold ownSliceDef
  iintro (%H | ⟨H, %Hc⟩)
  · exact absurd H.2 (List.cons_ne_nil _ _)
  · icases array_acc s.ptr 0 dq _ _ x (Int.le_refl 0) rfl $$ H with ⟨Hx, -⟩
    iapply hx $$ Hx

/-- A non-empty slice of strings is owned at a valid fraction (keeping it). -/
theorem ownSlice_string_valid (s : GoSlice) (dq : DFrac) (x : GoString) (xs : List GoString) :
    (s ↦*{dq} (x :: xs) : IProp GF) ⊢ ⌜✓ dq⌝ ∗ s ↦*{dq} (x :: xs) :=
  persistent_entails_right (ownSlice_string_valid' s dq x xs)

/-- A slice of strings at any fraction and an owned one, both at one fraction (for
`slices.Concat`), with the first's return. -/
theorem ownSlice_string_common (s t : GoSlice) (dq : DFrac) (xs ys : List GoString) :
    (s ↦*{dq} xs ∗ t ↦* ys : IProp GF) ⊢ |==> ∃ dq' : DFrac, s ↦*{dq'} xs ∗ t ↦*{dq'} ys ∗
      (s ↦*{dq'} xs -∗ s ↦*{dq} xs) := by
  cases xs with
  | nil =>
    iintro ⟨Hs, Ht⟩
    imodintro
    iexists DFrac.own 1
    iframe Ht
    isplitl [Hs]
    · iapply ownSlice_nil_frac $$ Hs
    · iintro Hs
      iapply ownSlice_nil_frac $$ Hs
  | cons x xs =>
    iintro ⟨Hs, Ht⟩
    icases ownSlice_string_valid s dq x xs $$ Hs with ⟨%Hv, Hs⟩
    imod ownSlice_update_to_dfrac dq t ys Hv $$ Ht with Ht
    imodintro
    iexists dq
    iframe Hs Ht
    iintro Hs; iexact Hs

end slices

end authorizer
end EtcdGrove
end Perennial
