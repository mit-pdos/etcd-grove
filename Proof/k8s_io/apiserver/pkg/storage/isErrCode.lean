/-
The proof of `storage.isErrCode`: `nil` is no `*StorageError`; else the type assertion, and the
code's comparison.
-/
module

public import Spec.k8s_io.apiserver.pkg.storage.isErrCode

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.apiserver.pkg.storage.Assumptions]

theorem storage.isErrCode.wp_proof : storage.isErrCode.spec (GF := GF) (hG := hG) := by
  intro err dq c code
  wp_start as H
  cases c with
  | none =>
    rw [show decide ((none : Option w64) = some code) = false by simp]
    unfold k8s.errCodeAt
    icases H with %Hn
    rcases Hn with rfl | ⟨ii, rfl, hty⟩
    · wp_auto
      iapply HΦ
      ipureintro; left; rfl
    · wp_auto
      simp only [hty, ↓reduceIte, decide_false]
      wp_auto
      iapply HΦ
      ipureintro; right; exact ⟨ii, rfl, hty⟩
  | some c =>
    unfold k8s.errCodeAt
    icases H with ⟨%l, %s, ⟨%he, %hc⟩, Hl⟩
    subst he
    icases (typedPointsto_not_null_dup _ _ _) $$ Hl with ⟨Hl, %Hn⟩
    iStructNamed Hl
    wp_auto
    ihave Hl : l ↦{dq} s $$ [Code Key ResourceVersion err]
    · iapply typedPointsto_combine l _ _ Hn
      simp only [TypedPointsto.typedPointstoDef]
      iframe
    subst hc
    have : decide (some s.Code' = some code) = decide (s.Code' = code) := by simp
    rw [this]
    iapply HΦ
    iexists l, s
    iframe Hl
    ipureintro; exact ⟨rfl, rfl⟩

end proof

end EtcdGrove
end Perennial
