/-
Proof of `Spec/go_opentelemetry_io/otel/trace/WithAttributes.lean` over the real body (2026-11-18; it
was a trust-boundary axiom while otel's `trace` was names-only): `WithAttributes(kvs...)` converts
the slice to `attributeOption`, then to the interface `SpanStartEventOption`. Lean-first.
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
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_opentelemetry_io.otel.trace.Assumptions]

theorem trace.WithAttributes.wp_proof : trace.WithAttributes.spec (GF := GF) (hG := hG) := by
  intro kvs
  wp_start as #Hinit
  wp_auto
  iapply HΦ
  itrivial

end proof

end EtcdGrove
end Perennial
