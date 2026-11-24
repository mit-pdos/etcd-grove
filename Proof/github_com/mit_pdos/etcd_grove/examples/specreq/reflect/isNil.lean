/-
`isNil` (see its spec): proved over Perennial's model of `reflect` (reflect S0).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.specreq.reflect.isNil
public import Perennial.Proof.reflect.Link
public import Perennial.Proof.reflect.Results

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace specreq_reflect

open Iris Iris.BI Iris.ProofMode github_com.mit_pdos.etcd_grove.examples.specreq.reflect

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.specreq.reflect.Assumptions]

theorem isNil.wp_proof :
    isNil.spec (GF := GF) (hG := hG) := by
  intro msg
  wp_start as %Hmsg
  wp_auto
  rcases Hmsg with rfl | ⟨T, p, rfl⟩
  · wp_auto
    iapply HΦ
    ipureintro
    simp
  · wp_auto
    wp_apply (_root_.Perennial.reflect.wp_ValueOf_reflPtr T p) as %w %Hw
    subst Hw
    wp_pures
    wp_apply (_root_.Perennial.reflect.Value.wp_IsNil.1 _ (t := go.PointerType T) (e := T) p (by simp only; rfl) (by simp only; rfl) rfl)
    iapply HΦ
    ipureintro
    constructor
    · intro h
      right
      simp only [decide_eq_true_eq] at h
      subst h
      exact ⟨T, rfl⟩
    · rintro (h | ⟨T', h⟩)
      · exact absurd h (by simp [interface.mkOk])
      · simp [interface.mkOk] at h
        simp [go.intoVal_inj h.2]

end proof

end specreq_reflect
end EtcdGrove
end Perennial
