/-
The trust boundary of `sort.SliceStable` (see its spec, `Spec/sort/SliceStable.lean`).
-/
module

public import Spec.sort.SliceStable

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

/-- **Trust-boundary assumption** (an axiom, not a proof): Go's `sort.SliceStable`, with a `less` implementing a strict weak order, leaves the slice at a
sorted permutation of its contents. Why that is true of Go is in the
spec's file header. -/
axiom sort.SliceStable.wp_proof : sort.SliceStable.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
