/-
The proof of `time.Duration.Seconds`, over Perennial's (`float64(d / Second) + float64(d % Second) /
1e9`, translated: some `float64`, under no premise). Lean-first.
-/
module

public import Spec.time.Duration__Seconds
public import Perennial.Spec.time.Duration__Seconds
import Perennial.Proof.time.Duration__Seconds

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
variable [package_sem : _root_.Perennial.time.Assumptions]

theorem time.Duration.Seconds.wp_proof : time.Duration.Seconds.spec (GF := GF) (hG := hG) := by
  intro d
  wp_start_folded
  wp_apply _root_.Perennial.time.Duration.Seconds.wp_proof d as %f -
  iapply HΦ $$ %f
  itrivial

end proof

end EtcdGrove
end Perennial
