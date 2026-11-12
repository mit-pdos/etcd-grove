/-
The trust boundary of `bytes.Buffer.Bytes` (see its spec).
-/
module

public import Spec.bytes.Buffer__Bytes

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

axiom bytes.Buffer.Bytes.wp_proof : bytes.Buffer.Bytes.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
