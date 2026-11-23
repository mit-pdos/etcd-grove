/-
`maps.Clone` at `map[string]bool` (see its spec, `Spec.maps.Clone`), from Perennial's translation of
`maps` and its spec (`maps.wp_Clone_string_bool`, Perennial `70706ce5e`). Until 2026-11-23 a trust-boundary
axiom (reviewed: `notes/axiom-review/k8s-7g-trust.md`).
-/
module

public import Spec.maps.Clone
public import Perennial.Proof.maps.Results

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
variable [package_sem : _root_.Perennial.maps.Assumptions]

/-- `maps.Clone` at `map[string]bool`, from Perennial's spec (the `isPkgInit` premise is framed). -/
theorem maps.Clone.wp_proof_strBool : maps.Clone.spec_strBool (GF := GF) (hG := hG) := by
  intro m M dq
  iintro %Φ ⟨-, Hm⟩ HΦ
  iapply (_root_.Perennial.maps.wp_Clone_string_bool m dq M) $$ Hm HΦ

end proof

end EtcdGrove
end Perennial
