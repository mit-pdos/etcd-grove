/-
`reflect.Value.IsNil` of a `reflElem` of a slice type (see its spec): proved over Perennial's model of
`reflect` (reflect S0).
-/
module

public import Spec.reflect.Value__IsNil
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

theorem reflect.Value.IsNil.wp_proof :
    reflect.Value.IsNil.spec (GF := GF) (hG := hG) := by
  intro vp dq dq' v T p s
  wp_start as ⟨Hvp, %Hel, Hp⟩
  wp_auto
  obtain ⟨k, hk, rfl⟩ := Hel
  rw [go.is_underlying] at hk
  cases hk
  wp_apply (_root_.Perennial.reflect.Value.wp_IsNil.2.1 _ (t := go.SliceType T) (e := T) p dq' s (by simp only; rfl) rfl) $$ [$Hp]
  iintro Hp
  iapply HΦ
  iframe
  ipureintro
  constructor
  · intro h; simp at h; subst h; rfl
  · intro h; simpa using h

end proof

end EtcdGrove
end Perennial
