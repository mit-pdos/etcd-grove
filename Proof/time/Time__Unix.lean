/-
`time.Time.Unix`, proved over Perennial's translation of Go's.
-/
module

public import Spec.time.Time__Unix
public import Perennial.Proof.time.Link

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
variable [package_sem : time.Assumptions]

theorem time.Time.Unix.wp_proof : time.Time.Unix.spec (GF := GF) (hG := hG) := by
  intro t
  iintro %Φ - HΦ
  wp_apply _root_.Perennial.time.Time.wp_Unix as %n -
  iapply HΦ; itrivial

end proof

end EtcdGrove
end Perennial
