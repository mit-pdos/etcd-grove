/-
The trust boundary: `time.Duration.String` (not in Perennial's translation of `time`; total, and
it reads only its receiver).
-/
module

public import Spec.time.Duration__String

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : _root_.Perennial.time.Assumptions]

/-- **The trust boundary**: Go's `Duration.String` formats the duration into a local buffer
and returns it as a string; it does not panic and touches no other memory. -/
axiom time.Duration.String.wp_proof : time.Duration.String.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
