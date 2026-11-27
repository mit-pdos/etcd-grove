/-
The proof of `Spec/google_golang_org/grpc/metadata/fromOutgoingContextRaw.lean`, over grpc's translated
body (`metadata.go`).
-/
module

public import Spec.google_golang_org.grpc.metadata.fromOutgoingContextRaw

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
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : google_golang_org.grpc.metadata.Assumptions]

theorem metadata.fromOutgoingContextRaw.wp_proof :
    metadata.fromOutgoingContextRaw.spec (GF := GF) (hG := hG) := by
  intro ctx v ro hv
  wp_start as #Hv
  iunfold context.valueAt at Hv
  wp_auto
  wp_apply Hv as %w %hw
  subst hw
  cases ro with
  | some r =>
    simp only at hv
    subst hv
    simp only [interface.mkOk, ↓reduceIte, decide_true]
    wp_auto
    iapply HΦ
    ipureintro
    exact ⟨rfl, rfl, rfl⟩
  | none =>
    simp only at hv
    cases w with
    | nil =>
      wp_auto
      iapply HΦ
      ipureintro; rfl
    | ok wi =>
      have hty := hv wi rfl
      wp_auto
      simp only [hty, ↓reduceIte]
      wp_auto
      iapply HΦ
      ipureintro; rfl

end proof

end EtcdGrove
end Perennial
