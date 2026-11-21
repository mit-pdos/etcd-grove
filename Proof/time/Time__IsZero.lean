/-
`(*time.Time).IsZero`, proved over Perennial's translation of Go's `Time.IsZero` (the pointer method loads the time).
-/
module

public import Spec.time.Time__IsZero
public import Perennial.Proof.time.Link

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

theorem time.Time.IsZero.wp_proof : time.Time.IsZero.spec (GF := GF) (hG := hG) := by
  intro p t dq
  wp_start as Hp
  wp_auto
  wp_apply _root_.Perennial.time.Time.wp_IsZero
  iapply HΦ; iexact Hp

end proof

end EtcdGrove
end Perennial
