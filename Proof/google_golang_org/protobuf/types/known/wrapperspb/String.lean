/- Lean-first (no Rocq counterpart).

# `wrapperspb.String`'s proof

A composite literal `&StringValue{Value: v}`: its other fields zero, so no unknown fields.
-/
module

public import Spec.google_golang_org.protobuf.types.known.wrapperspb.String

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : google_golang_org.protobuf.types.known.wrapperspb.Assumptions]

theorem google_golang_org.protobuf.types.known.wrapperspb.String.wp_proof :
    google_golang_org.protobuf.types.known.wrapperspb.String.spec (GF := GF) (hG := hG) := by
  intro v hv
  wp_start
  wp_auto
  iapply HΦ
  simp only [EtcdGrove.stringValueSend, EtcdGrove.stringValueSendB]
  iexists _
  iframe
  ipureintro
  exact ⟨rfl, rfl, hv⟩

end proof

end Perennial
