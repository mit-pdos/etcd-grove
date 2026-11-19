/-
`Set[T].Clone()` (`set.go`): a copy. Lean-first; for the union builder's `ToDecision`. Its proof
(unfinished). Lean-first (no Rocq counterpart).
-/
module

public import Spec.k8s_io.apimachinery.pkg.util.sets.Set__Clone

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace sets

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode k8s_io.apimachinery.pkg.util.sets

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.apimachinery.pkg.util.sets.Assumptions]

theorem Set.Clone.wp_proof :
    Set.Clone.spec (GF := GF) (hG := hG) := by
  sorry

end proof

end sets
end EtcdGrove
end Perennial
