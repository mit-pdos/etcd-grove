/-
`math.Ceil`: Perennial's proof of the real Go (`math.wp_Ceil`: `archCeil` on amd64, assembly with a
trusted model returning an arbitrary bit pattern, `Perennial/TrustedCode/math.lean`).
-/
module

public import Spec.math.Ceil
public import Perennial.Proof.math.Link

@[expose] public section

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

theorem math.Ceil.wp_proof : math.Ceil.spec (GF := GF) (hG := hG) :=
  _root_.Perennial.math.wp_Ceil

end proof

end EtcdGrove
end Perennial
