/-
Proof of `tracing.Span.End`'s spec: from the span's `tracing.isSpan` (until 2026-11-06 an axiom on
any non-nil `*Span`, false: see the spec's file header).
-/
module

public import Spec.k8s_io.component_base.tracing.Span__End

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

theorem tracing.Span.End.wp_proof : tracing.Span.End.spec (GF := GF) (hG := hG) := by
  intro sp d
  iintro %Φ ⟨-, #Hsp⟩ HΦ
  unfold tracing.isSpan
  icases Hsp with ⟨#HEnd, -⟩
  iapply HEnd
  · itrivial
  iexact HΦ

end proof

end EtcdGrove
end Perennial
