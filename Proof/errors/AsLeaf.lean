/-
The trust boundary: `errors.As` of an `errors.New` error against a target type whose type set
does not contain `*errorString` (Perennial's `errors.As.spec` allows any result). Go's `As`
(`errors/wrap.go`) returns `false` for a nil error, else walks `err`'s tree: `err` is not
assignable to the target's type (its type is not in the type set), it has no `As` method, and no
`Unwrap` method ends the walk with `false`, the target not written.
-/
module

public import Spec.errors.AsLeaf

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : _root_.Perennial.errors.Assumptions]

axiom errors.AsLeaf.wp_proof : errors.AsLeaf.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
