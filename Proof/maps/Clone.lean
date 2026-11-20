/-
The trust boundary of `maps.Clone` (see its spec, `Spec.maps.Clone`; reviewed:
`notes/axiom-review/k8s-7g-trust.md`).
-/
module

public import Spec.maps.Clone

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

/-- **Trust-boundary assumption** (an axiom, not a proof): `maps.Clone` of a non-nil `map[string]bool` returns a fresh map with the same entries; why that is true of Go is in the
spec's file header, with its Go tests. -/
axiom maps.Clone.wp_proof_strBool : maps.Clone.spec_strBool (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
