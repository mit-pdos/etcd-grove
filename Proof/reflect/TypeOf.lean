/-
`reflect.TypeOf` (see its spec): proved over Perennial's model of `reflect` (reflect S0), from the
trust-boundary spec of `rtype.String`.
-/
module

public import Spec.reflect.TypeOf
public import Spec.reflect.rtype__String
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

theorem reflect.TypeOf.wp_proof
    (wp_String : reflect.rtype.String.spec (GF := GF) (hG := hG)) :
    reflect.TypeOf.spec (GF := GF) (hG := hG) := by
  intro x
  iintro %Φ ⟨#Hinit, %Hx⟩ HΦ
  obtain ⟨t, v, rfl, ht⟩ := Hx
  wp_apply ((_root_.Perennial.reflect.wp_TypeOf (GF := GF) (hG := hG)).1 t v ht) $$ [$Hinit]
  iapply HΦ
  imodintro
  iintro %Φ'
  imodintro
  iintro _ HΦ'
  wp_pures
  wp_apply wp_String
  iexact HΦ'

end proof

end EtcdGrove
end Perennial
