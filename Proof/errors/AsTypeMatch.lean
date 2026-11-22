/-
Proof of `Spec/errors/AsTypeMatch.lean`: `AsType` calls `asType`, whose loop's first type assertion
`err.(T)` succeeds and returns. Lean-first.
-/
module

public import Spec.errors.AsTypeMatch

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : _root_.Perennial.errors.Assumptions]

theorem errors.AsTypeMatch.wp_proof : errors.AsTypeMatch.spec (GF := GF) (hG := hG) := by
  intro ii T' _ _ T _ x hI hty hv
  wp_start
  wp_auto
  wp_func_call
  wp_call
  wp_auto
  ihave HI : (err_ptr ↦ GoInterface.ok ii : IProp GF) $$ [err]
  · iexact err
  wp_for HI
  haveI : T ↓u underlying T := ⟨rfl⟩
  wp_auto
  subst hty
  simp only [hI, hv, Bool.false_eq_true, ↓reduceIte, decide_true]
  wp_auto
  wp_for_post
  iapply HΦ
  itrivial

end proof

end EtcdGrove
end Perennial
