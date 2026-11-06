/-
The trust boundary of `sort.SliceIsSorted` (see its spec).
-/
module

public import Spec.sort.SliceIsSorted

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

/-- **Trust-boundary assumption** (an axiom, not a proof): Go's `sort.SliceIsSorted` on a slice
returns whether no element is `less` than the one before it, calling `less` only on indices of
the slice; why that is true of Go is in the spec's file header. -/
axiom sort.SliceIsSorted.wp_proof : sort.SliceIsSorted.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
