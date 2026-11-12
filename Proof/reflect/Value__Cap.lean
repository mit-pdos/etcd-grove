/-
The trust boundary of `reflect.Value.Cap` (see its spec).
-/
module

public import Spec.reflect.Value__Cap

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
variable [reflect.Assumptions]

axiom reflect.Value.Cap.wp_proof : reflect.Value.Cap.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
