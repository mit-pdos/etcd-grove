/-
`strings.Contains`: Perennial's proof of the real Go (`strings.wp_Contains`).
-/
module

public import Spec.strings.Contains
public import Perennial.Proof.strings.Link

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : _root_.Perennial.strings.Assumptions]

theorem strings.Contains.wp_proof : strings.Contains.spec (GF := GF) (hG := hG) :=
  _root_.Perennial.strings.wp_Contains

end proof

end EtcdGrove
end Perennial
