/-
The trust boundary of `reflect.DeepEqual` (see its spec, `Spec.reflect.DeepEqualK8s`; reviewed:
`notes/axiom-review/k8s-7g-trust.md`).
-/
module

public import Spec.reflect.DeepEqualK8s

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

/-- **Trust-boundary assumption** (an axiom, not a proof): Go's `reflect.DeepEqual` on the checker's values (interface values, `correctness.Response`, `map[string]runtime.Object`) of `k8sDeep.DeepV` deep values returns whether the deep values are equal, and `false` on a `Response` with a
`*StatusError` error against one with deep values (clause 4); why that is true of Go is in the
spec's file header, with its Go tests. -/
axiom reflect.DeepEqual.wp_proof_k8s : reflect.DeepEqual.spec_k8s (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
