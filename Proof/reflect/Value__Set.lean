/-
The trust boundary of `reflect.Value.Set` (see its spec).
-/
module

public import Spec.reflect.Value__Set

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [reflect.Assumptions]

axiom reflect.Value.Set.wp_proof : reflect.Value.Set.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
