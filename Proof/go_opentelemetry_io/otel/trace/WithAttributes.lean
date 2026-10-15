/-
The trust boundary: `trace.WithAttributes` (otel's span options are names-only; building one has no effect the model sees).
-/
module

public import Spec.go_opentelemetry_io.otel.trace.WithAttributes

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

axiom trace.WithAttributes.wp_proof : trace.WithAttributes.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
