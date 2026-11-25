/-
Proof of `Spec/google_golang_org/protobuf/types/known/wrapperspb/String.lean`. Lean-first (no Rocq
counterpart).
-/
module

public import Spec.google_golang_org.protobuf.types.known.wrapperspb.String

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode google_golang_org.protobuf.types.known

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [pkg_wr : google_golang_org.protobuf.types.known.wrapperspb.Assumptions]

theorem wrapperspb.String.wp_proof : wrapperspb.String.spec (GF := GF) (hG := hG) := by
  intro v
  wp_start
  wp_auto
  iapply HΦ
  iexists _
  iframe
  ipureintro
  exact ⟨rfl, rfl⟩

end proof

end EtcdGrove
end Perennial
