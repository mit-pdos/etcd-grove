/-
The trust boundary: `time.Duration.Seconds` (a float division, outside Perennial's `time` model; total).
-/
module

public import Spec.time.Duration__Seconds

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

axiom time.Duration.Seconds.wp_proof : time.Duration.Seconds.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
