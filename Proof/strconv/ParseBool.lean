/-
`strconv.ParseBool`, proved over Perennial's translation of Go's.
-/
module

public import Spec.strconv.ParseBool
public import Perennial.Proof.strconv.Link

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : _root_.Perennial.strconv.Assumptions]

theorem strconv.ParseBool.wp_proof : strconv.ParseBool.spec (GF := GF) (hG := hG) := by
  intro str
  iintro %Φ #Hpkg HΦ
  wp_apply _root_.Perennial.strconv.wp_ParseBool as %b %err -
  iapply HΦ; itrivial

end proof

end EtcdGrove
end Perennial
