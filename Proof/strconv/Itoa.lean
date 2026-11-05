/-
The trust boundary: `strconv.Itoa` (Perennial's `strconv` is names-only; Go's `Itoa(i)` is `FormatInt(int64(i), 10)`; K4 of `notes/k8s-compactor-plan.md`, the compactor example's writer).
-/
module

public import Spec.strconv.Itoa

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

axiom strconv.Itoa.wp_proof : strconv.Itoa.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
