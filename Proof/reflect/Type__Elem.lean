/-
`reflect.Type.Elem` of the `Type` of a slice type (see its spec): proved over Perennial's model of
`reflect` (reflect S0).
-/
module

public import Spec.reflect.Type__Elem
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

theorem reflect.Type.Elem.wp_proof :
    reflect.Type.Elem.spec (GF := GF) (hG := hG) := by
  intro rt T
  wp_start as %Hrt
  subst Hrt
  wp_pures
  rw [show go.tok (go.SliceType T) = interface.mkOk (go.PointerType (go.SliceType T)) #null from rfl]
  wp_apply (_root_.Perennial.reflect.rtype.wp_Elem (T := go.SliceType T) T null (by simp [go.typeQuery, go.is_underlying]))
  iapply HΦ
  ipureintro
  rfl

end proof

end EtcdGrove
end Perennial
