/-
`reflect.ValueOf` of an interface holding a pointer, and the `IsNil` and `Elem` of the result (see its spec): proved over Perennial's model of
`reflect` (reflect S0).
-/
module

public import Spec.reflect.ValueOf
public import Perennial.Proof.reflect.Link
public import Perennial.Proof.reflect.Results

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

theorem reflect.ValueOf.wp_proof :
    reflect.ValueOf.spec (GF := GF) (hG := hG) := by
  intro T p
  iintro %Φ #Hinit HΦ
  wp_apply (_root_.Perennial.reflect.wp_ValueOf_reflPtr T p) $$ [$Hinit] as %w %Hw
  subst Hw
  iapply HΦ
  isplit
  · imodintro
    iintro %Φ'
    imodintro
    iintro _ HΦ'
    wp_pures
    wp_apply (_root_.Perennial.reflect.Value.wp_IsNil.1 _ (t := go.PointerType T) (e := T) p (by simp only; rfl) (by simp only; rfl) rfl)
    iapply HΦ'
    itrivial
  · imodintro
    iintro %Φ'
    imodintro
    iintro %Hpre HΦ'
    obtain ⟨hp, k, hk⟩ := Hpre
    wp_pures
    wp_apply (_root_.Perennial.reflect.Value.wp_Elem _ T k p hk rfl rfl (by simp only; rfl) (by simp only; rfl))
    rw [if_neg hp]
    iapply HΦ'
    ipureintro
    refine ⟨k, hk, ?_⟩
    simp only
    rw [(reflectM.elemFlag_bits k (reflectM.kindOf_lt hk)).2.2.2]

end proof

end EtcdGrove
end Perennial
