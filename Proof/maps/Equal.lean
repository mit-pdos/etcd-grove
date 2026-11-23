/-
`maps.Equal` at `map[string]bool` (see its spec, `Spec.maps.Equal`), from Perennial's translation of
`maps` and its spec (`maps.wp_Equal_string_bool`, Perennial `70706ce5e`). Until 2026-11-23 a trust-boundary
axiom (reviewed: `notes/axiom-review/k8s-7g-trust.md`).
-/
module

public import Spec.maps.Equal
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

/-- `maps.Equal` at `map[string]bool`, from Perennial's spec (the `isPkgInit` premise is framed). -/
theorem maps.Equal.wp_proof_strBool : maps.Equal.spec_strBool (GF := GF) (hG := hG) := by
  intro m1 m2 M1 M2 dq1 dq2
  iintro %Φ ⟨-, Hm1, Hm2⟩ HΦ
  iapply (_root_.Perennial.maps.wp_Equal_string_bool m1 m2 dq1 dq2 M1 M2) $$ [Hm1 Hm2] HΦ
  iframe

end proof

end EtcdGrove
end Perennial
