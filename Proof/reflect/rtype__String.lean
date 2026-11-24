/-
The trust boundary of `reflect.rtype.String` (see its spec).
-/
module

public import Spec.reflect.rtype__String

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

axiom reflect.rtype.String.wp_proof : reflect.rtype.String.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
