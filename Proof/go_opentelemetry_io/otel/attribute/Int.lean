/-
The trust boundary: `attribute.Int` (otel's attributes are names-only; building one has no effect the model sees).
-/
module

public import Spec.go_opentelemetry_io.otel.attribute.Int

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
variable [package_sem : go_opentelemetry_io.otel.«attribute».Assumptions]

axiom «attribute».Int.wp_proof : «attribute».Int.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
