/-
The trust boundary of `reflect.rtype.String` (see its spec).

It holds only while `rtype.String` is names-only in Perennial's reflect model (`Code/reflect.toml`'s
`names_only`: no `MethodUnfold` for it). The model's Go body is `gomodel.Stuck()`: when a later
stage models it, retire this axiom (prove the spec from the body); it must never stand beside a
`MethodUnfold` to the stuck body, which it would contradict. Reviewed (axiom skill, 2026-11-24):
sound; Go's `(*rtype).String()` never panics on a non-nil type, and the model's `rtype.mk (go.tok T)`
is never nil.
-/
module

public import Spec.reflect.rtype__String

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

axiom reflect.rtype.String.wp_proof : reflect.rtype.String.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
