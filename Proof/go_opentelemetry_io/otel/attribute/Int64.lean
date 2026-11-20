/-
Proof of `Spec/go_opentelemetry_io/otel/attribute/Int64.lean` over the real body (2026-11-18; it
was a trust-boundary axiom while the package was names-only): `Int64(k, v)` is
`Key(k).Int64(v)`, a `KeyValue` literal over the `Value` constructor. Lean-first.
-/
module

public import Spec.go_opentelemetry_io.otel.attribute.Int64

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_opentelemetry_io.otel.«attribute».Assumptions]

theorem «attribute».Int64.wp_proof : «attribute».Int64.spec (GF := GF) (hG := hG) := by
  intro k v
  wp_start as #Hinit
  haveI : go.NotInterface go.string := ⟨trivial⟩
  repeat (first | wp_auto | (wp_method_call; wp_call) | (wp_func_call; wp_call))
  iapply HΦ
  itrivial

end proof

end EtcdGrove
end Perennial
