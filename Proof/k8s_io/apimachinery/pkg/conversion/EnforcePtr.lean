/-
The trust boundary of `conversion.EnforcePtr` (see its spec).
-/
module

public import Spec.k8s_io.apimachinery.pkg.conversion.EnforcePtr

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

axiom conversion.EnforcePtr.wp_proof : conversion.EnforcePtr.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
