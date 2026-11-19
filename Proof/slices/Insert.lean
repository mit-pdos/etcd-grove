/-
The trust boundary of `slices.Insert` (see its spec, `Spec/slices/Insert.lean`).
-/
module

public import Spec.slices.Insert

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

/-- **Trust-boundary assumption** (an axiom, not a proof): Go's `slices.Insert(s, i, v...)` returns a slice holding `s[:i] ++ v ++ s[i:]`, with its
capacity. Why that is true of Go is in the
spec's file header. -/
axiom slices.Insert.wp_proof : slices.Insert.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
