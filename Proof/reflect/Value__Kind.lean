/-
`reflect.Value.Kind` of a `reflElem` of a slice type (see its spec): proved over Perennial's model of
`reflect` (reflect S0).
-/
module

public import Spec.reflect.Value__Kind
public import Perennial.Spec.reflect.Value__Kind

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
variable [reflect.Assumptions]

theorem reflect.Value.Kind.wp_proof
    (hK : _root_.Perennial.reflect.Value.Kind.spec (GF := GF) (hG := hG)) :
    reflect.Value.Kind.spec (GF := GF) (hG := hG) := by
  intro vp dq v T p
  wp_start as ⟨Hvp, %Hel⟩
  wp_auto
  obtain ⟨k, hk, rfl⟩ := Hel
  rw [go.is_underlying] at hk
  cases hk
  wp_apply hK
  rw [show (W64 ↑(23 : Nat) ||| W64 128 ||| W64 256) &&& W64 31 = W64 23 by decide]
  iapply HΦ
  iexact Hvp

end proof

end EtcdGrove
end Perennial
