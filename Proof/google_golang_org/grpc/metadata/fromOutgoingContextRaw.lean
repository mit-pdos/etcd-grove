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
  intro ctx v hv
  wp_start as #Hv
  iunfold context.valueAt at Hv
  wp_auto
  wp_apply Hv as %w %hw
  subst hw
  cases w with
  | nil =>
    wp_auto
    iapply HΦ
    ipureintro
    intro vi h; cases h
  | ok wi =>
    by_cases hty : wi.ty = google_golang_org.grpc.metadata.rawMD.ty
    · obtain ⟨r, hr⟩ := hv wi rfl hty
      simp only [hty, hr, ↓reduceIte, decide_true]
      wp_auto
      iapply HΦ
      ipureintro
      simp only [↓reduceIte]
      cases wi
      simp_all
    · wp_auto
      simp only [hty, ↓reduceIte]
      wp_auto
      iapply HΦ
      ipureintro
      intro vi h; cases h; exact hty

end proof

end EtcdGrove
end Perennial
