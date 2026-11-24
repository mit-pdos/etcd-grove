/-
`MustPanicIsNilZeroValue` (see its spec): proved over Perennial's model of `reflect` (reflect S0).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.specreq.reflect.MustPanicIsNilZeroValue
public import Perennial.Proof.reflect.Link

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

theorem MustPanicIsNilZeroValue.wp_proof :
    MustPanicIsNilZeroValue.spec (GF := GF) (hG := hG) := by
  have hz : (zero_val _root_.Perennial.reflect.Value).flag' = W64 0 := rfl
  wp_start
  wp_auto
  wp_apply _root_.Perennial.reflect.wp_ValueOf.2.2
  wp_pures
  wp_apply (_root_.Perennial.reflect.Value.wp_IsNil.2.2 _)
  · rw [hz, show (W64 0 &&& W64 31 : w64) = W64 0 by decide]; simp
  iintro %l Hl
  wp_pures
  rw [hz, show (W64 0 &&& W64 31 : w64) = W64 0 by decide]
  iapply HΦ
  iexists l
  iframe
  ipureintro
  rfl

end proof

end specreq_reflect
end EtcdGrove
end Perennial
