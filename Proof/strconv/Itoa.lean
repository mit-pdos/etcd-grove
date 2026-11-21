/-
`strconv.Itoa`, proved over Perennial's translation of Go's (stdlib2, 2026-11-21; until then a
trust-boundary axiom).
-/
module

public import Spec.strconv.Itoa
public import Perennial.Proof.strconv.Link

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
variable [package_sem : _root_.Perennial.strconv.Assumptions]

theorem strconv.Itoa.wp_proof : strconv.Itoa.spec (GF := GF) (hG := hG) := by
  intro i
  iintro %Φ #Hpkg HΦ
  wp_apply _root_.Perennial.strconv.wp_Itoa i
  iapply HΦ; ipureintro; rfl

end proof

end EtcdGrove
end Perennial
