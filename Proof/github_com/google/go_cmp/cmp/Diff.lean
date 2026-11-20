/-
The trust boundary of `cmp.Diff` (see its spec, `Spec.github_com.google.go_cmp.cmp.Diff`; reviewed:
`notes/axiom-review/k8s-7g-trust.md`).
-/
module

public import Spec.github_com.google.go_cmp.cmp.Diff

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

/-- **Trust-boundary assumption** (an axiom, not a proof): go-cmp's `cmp.Diff` with no options on two `[]eventReference` returns `""` iff they have the same nil-ness and equal elements; why that is true of Go is in the
spec's file header, with its Go tests. -/
axiom cmp.Diff.wp_proof_eventRefs : cmp.Diff.spec_eventRefs (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
