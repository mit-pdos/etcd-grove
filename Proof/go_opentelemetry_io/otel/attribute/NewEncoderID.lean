/-
Proof of `Spec/go_opentelemetry_io/otel/attribute/NewEncoderID.lean` over the real body
(prove-otel-encoderid, 2026-11-25): `atomic.Uint64.Add(1)` (Perennial's `Uint64.wp_Add`) on the
owned counter, then the `EncoderID` literal. Lean-first.
-/
module

public import Spec.go_opentelemetry_io.otel.attribute.NewEncoderID
public import Perennial.Proof.sync.atomic.Link

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

theorem «attribute».NewEncoderID.wp_proof : «attribute».NewEncoderID.spec (GF := GF) (hG := hG) := by
  intro n
  wp_start as Hc
  wp_auto
  wp_apply _root_.Perennial.sync.atomic.Uint64.wp_Add _ (W64 1) $$ [$Hpkg]
  iapply fupd_mask_intro (show (∅ : CoPset) ⊆ ⊤ from Std.LawfulSet.empty_subset)
  iintro Hmask
  inext
  iexists n
  iframe Hc
  iintro Hc
  imod Hmask with -
  imodintro
  wp_auto
  have e : n + W64 1 = n + 1 := rfl
  rw [e]
  iapply HΦ
  iexact Hc

end proof

end EtcdGrove
end Perennial
