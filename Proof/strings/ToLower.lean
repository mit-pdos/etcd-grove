/-
The trust boundary of `strings.ToLower` (see its spec).
-/
module

public import Spec.strings.ToLower

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

/-- **Trust-boundary assumption** (an axiom, not a proof): Go's `strings.ToLower` returns some
string and never panics; why that is true of Go is in the spec's file header. -/
axiom strings.ToLower.wp_proof : strings.ToLower.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
