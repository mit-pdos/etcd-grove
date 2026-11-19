/-
The trust boundary of `slices.BinarySearchFunc` (see its spec, `Spec/slices/BinarySearchFunc.lean`).
-/
module

public import Spec.slices.BinarySearchFunc

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

/-- **Trust-boundary assumption** (an axiom, not a proof): Go's `slices.BinarySearchFunc`, with a `cmp` whose signs are non-decreasing along the slice,
returns the least index with a non-negative `cmp` and whether `cmp` is `0` there. Why that is true of Go is in the
spec's file header. -/
axiom slices.BinarySearchFunc.wp_proof : slices.BinarySearchFunc.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
