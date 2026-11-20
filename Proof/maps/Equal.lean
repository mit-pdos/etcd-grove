/-
The trust boundary of `maps.Equal` (see its spec, `Spec.maps.Equal`; reviewed:
`notes/axiom-review/k8s-7g-trust.md`).
-/
module

public import Spec.maps.Equal

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

/-- **Trust-boundary assumption** (an axiom, not a proof): `maps.Equal` of two non-nil `map[string]bool` returns whether they have the same entries; why that is true of Go is in the
spec's file header, with its Go tests. -/
axiom maps.Equal.wp_proof_strBool : maps.Equal.spec_strBool (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
