/-
The trust boundary of `reflect.DeepEqual` (see its spec).
-/
module

public import Spec.reflect.DeepEqual

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

/-- **Trust-boundary assumption** (an axiom, not a proof): Go's `reflect.DeepEqual` on two non-nil
`map[Pgid]struct{}` returns whether they have the same keys; why that is true of Go is in the spec's file header. -/
axiom reflect.DeepEqual.wp_proof_pgidSet : reflect.DeepEqual.spec_pgidSet (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
