/-
`rand.Int31`: Perennial's proof (`math.rand.wp_Int31`, Perennial 47ec64a9d). (The trust boundary, an
axiom, until 2026-11-24, rand-retire.)
-/
module

public import Spec.math.rand.Int31
public import Perennial.Proof.math.rand.Link

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
variable [package_sem : _root_.Perennial.math.rand.Assumptions]

theorem rand.Int31.wp_proof : rand.Int31.spec (GF := GF) (hG := hG) :=
  _root_.Perennial.math.rand.wp_Int31

end proof

end EtcdGrove
end Perennial
