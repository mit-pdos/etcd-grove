/-
The trust boundary of `reflect.New` (see its spec).
-/
module

public import Spec.reflect.New

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

axiom reflect.New.wp_proof : reflect.New.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
