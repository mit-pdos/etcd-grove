/-
The trust boundary of `reflect.TypeOf` (see its spec).
-/
module

public import Spec.reflect.TypeOf

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

axiom reflect.TypeOf.wp_proof : reflect.TypeOf.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
