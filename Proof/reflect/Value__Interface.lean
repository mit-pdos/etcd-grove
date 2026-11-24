/-
`reflect.Value.Interface` of a `reflPtr` (see its spec): proved over Perennial's model of
`reflect` (reflect S0).
-/
module

public import Spec.reflect.Value__Interface
public import Perennial.Proof.reflect.Link

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

theorem reflect.Value.Interface.wp_proof :
    reflect.Value.Interface.spec (GF := GF) (hG := hG) := by
  intro w T p
  wp_start as %Hw
  subst Hw
  wp_pures
  wp_apply (_root_.Perennial.reflect.Value.wp_Interface _ T p rfl rfl (by simp only; rfl) (by simp only; rfl))
  iapply HΦ
  itrivial

end proof

end EtcdGrove
end Perennial
