/-
The trust boundary of `reflect.DeepEqual` on two nil interfaces (see its spec,
`Spec/reflect/DeepEqualNil.lean`).
-/
module

public import Spec.reflect.DeepEqualNil

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

/-- **Trust-boundary assumption** (an axiom, not a proof): Go's `reflect.DeepEqual(nil, nil)`
returns `true` (`reflect/deepequal.go`: `if x == nil || y == nil { return x == y }`); see the spec's
file header. -/
axiom reflect.DeepEqual.wp_proofNil : reflect.DeepEqual.specNil (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
