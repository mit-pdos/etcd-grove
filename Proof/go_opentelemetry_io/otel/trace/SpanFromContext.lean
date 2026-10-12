/-
The trust boundary: `trace.SpanFromContext` (`go.opentelemetry.io/otel/trace` is names-only).
-/
module

public import Spec.go_opentelemetry_io.otel.trace.SpanFromContext

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_opentelemetry_io.otel

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

axiom trace.SpanFromContext.wp_proof : trace.SpanFromContext.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
