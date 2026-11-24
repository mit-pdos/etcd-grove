/-
`fmt.Sprintf` for arguments whose `Error()`/`String()` Go calls: Perennial's `fmt.wp_Sprintf`, of the
real `Sprintf` (real `fmt` stage 1, 2026-11-24; from 2026-11-20 its model's; until then an axiom
here).
-/
module

public import Spec.fmt.SprintfArgs
public import Perennial.Proof.fmt

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : _root_.Perennial.fmt.Assumptions]

theorem fmt.SprintfArgs.wp_proof : fmt.SprintfArgs.spec (GF := GF) (hG := hG) :=
  _root_.Perennial.fmt.wp_Sprintf

end proof

end EtcdGrove
end Perennial
