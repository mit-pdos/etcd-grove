/-
`strconv.FormatUint`, proved over Perennial's translation of Go's (stdlib2, 2026-11-21; until then a
trust-boundary axiom).
-/
module

public import RaftWitness.Spec.strconv.FormatUint
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

theorem strconv.FormatUint.wp_proof : strconv.FormatUint.spec (GF := GF) (hG := hG) := by
  intro i base
  iintro %Φ ⟨#Hpkg, %Hb⟩ HΦ
  wp_apply _root_.Perennial.strconv.wp_FormatUint i base Hb.1 Hb.2
  iapply HΦ; itrivial

end proof

end EtcdGrove
end Perennial
