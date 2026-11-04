/-
The trust boundary: `strconv.FormatInt` (Perennial's `strconv` is names-only; `FormatInt` of a base in `2..36` returns its digits with a leading `-` when negative; K2 of `notes/k8s-compactor-plan.md`, U2).
-/
module

public import Spec.strconv.FormatInt

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

axiom strconv.FormatInt.wp_proof : strconv.FormatInt.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
