/-
`math.Pow`: Perennial's proof of the real Go (`math.wp_Pow`: `pow`, translated, over `Exp`/`Log`'s
amd64 assembly with trusted models returning an arbitrary bit pattern, `Perennial/TrustedCode/math.lean`).
-/
module

public import Spec.math.Pow
public import Perennial.Proof.math.Link

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : _root_.Perennial.math.Assumptions]

theorem math.Pow.wp_proof : math.Pow.spec (GF := GF) (hG := hG) :=
  _root_.Perennial.math.wp_Pow

end proof

end EtcdGrove
end Perennial
