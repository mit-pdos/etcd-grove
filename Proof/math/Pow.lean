/-
The trust boundary: `math.Pow(x, y)` (names-only in Perennial's `math`; total, some `float64`).
Lean-first.
-/
module

public import Spec.math.Pow

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

axiom math.Pow.wp_proof : math.Pow.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
