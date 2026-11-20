/-
The trust boundary of `maps.Keys` (see its spec, `Spec.maps.Keys`; reviewed:
`notes/axiom-review/k8s-7g-trust.md`).
-/
module

public import Spec.maps.Keys

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

/-- **Trust-boundary assumption** (an axiom, not a proof): `slices.Sorted(maps.Keys(m))` on a `map[string]runtime.Object` returns the map's keys at the time of `Sorted`, each once, strictly increasing; why that is true of Go is in the
spec's file header, with its Go tests. -/
axiom maps.Keys.wp_proof_objMap : maps.Keys.spec_objMap (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
