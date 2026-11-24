/-
`reflect.Value.Type` of a `reflElem` (see its spec): proved over Perennial's model of `reflect`
(reflect S0).
-/
module

public import Spec.reflect.Value__Type
public import Perennial.Spec.reflect.Value__Type

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

theorem reflect.Value.Type.wp_proof
    (hT : _root_.Perennial.reflect.Value.Type.spec (GF := GF) (hG := hG)) :
    reflect.Value.Type.spec (GF := GF) (hG := hG) := by
  intro vp dq v T p
  wp_start as ⟨Hvp, %Hel⟩
  wp_auto
  obtain ⟨k, hk, rfl⟩ := Hel
  have hb := reflectM.elemFlag_bits k (reflectM.kindOf_lt hk)
  wp_apply hT _ hb.2.1 hb.2.2.1
  iapply HΦ
  iframe
  ipureintro
  rfl

end proof

end EtcdGrove
end Perennial
