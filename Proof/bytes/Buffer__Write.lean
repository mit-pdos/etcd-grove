/-
The trust boundary of `bytes.Buffer.Write` (see its spec).
-/
module

public import Spec.bytes.Buffer__Write

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
variable [bytes.Assumptions]

axiom bytes.Buffer.Write.wp_proof : bytes.Buffer.Write.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
