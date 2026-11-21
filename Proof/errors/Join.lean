/-
`errors.Join`, proved over Perennial's translation of Go's (whose spec says more: `nil` exactly when every error is `nil`).
-/
module

public import Spec.errors.Join
public import Perennial.Proof.errors.Link

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
variable [package_sem : _root_.Perennial.errors.Assumptions]

theorem errors.Join.wp_proof : errors.Join.spec (GF := GF) (hG := hG) := by
  intro sl dq es
  iintro %Φ Hs HΦ
  wp_apply _root_.Perennial.errors.wp_Join $$ Hs as %e ⟨%He, Hs⟩
  iapply HΦ
  iframe
  ipureintro
  exact He.2

end proof

end EtcdGrove
end Perennial
