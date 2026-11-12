/-
The trust boundary of `reflect.Value.Addr` (see its spec).
-/
module

public import Spec.reflect.Value__Addr

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

axiom reflect.Value.Addr.wp_proof : reflect.Value.Addr.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
