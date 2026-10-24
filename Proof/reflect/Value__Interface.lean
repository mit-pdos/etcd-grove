/-
The trust boundary of `reflect.Value.Interface` (see its spec).
-/
module

public import Spec.reflect.Value__Interface

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

axiom reflect.Value.Interface.wp_proof : reflect.Value.Interface.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
