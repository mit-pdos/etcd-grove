/-
`(*field.ErrorList).ToAggregate()`: the proof of its spec from the value method's (goose's
`ptr_unfold'ToAggregate`, since `ToAggregate` is translated with its body; until 2026-11-19 a
trust-boundary workaround axiom). Lean-first (no Rocq counterpart).
-/
module

public import Spec.k8s_io.apimachinery.pkg.util.validation.field.ErrorList__ToAggregate_ptr

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace field

open Iris Iris.BI Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : _root_.Perennial.k8s_io.apimachinery.pkg.util.validation.field.Assumptions]

/-- Go puts `ErrorList`'s value methods in the method set of `*ErrorList`: `l.ToAggregate()` loads
`*l` (goose's `ptr_unfold'ToAggregate`) and runs the value method on it (its spec, a hypothesis). -/
theorem ErrorList.ToAggregate_ptr.wp_proof
    (wp_ToAggregate : ErrorList.ToAggregate.spec (GF := GF) (hG := hG)) :
    ErrorList.ToAggregate_ptr.spec (GF := GF) (hG := hG) := by
  intro l dl s dq errs
  wp_start as ⟨Hl, Hs, #Herrs⟩
  wp_auto
  wp_apply wp_ToAggregate $$ [$Hs] as %a ⟨Hs, #Ha⟩
  · iexact Herrs
  iapply HΦ; iframe; iexact Ha

end proof

end field
end EtcdGrove
end Perennial
