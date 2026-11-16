/-
The trust boundary: `errors.As` of a leaf error (no `As`, no `Unwrap` method) whose type is outside
the target's type set and, for a non-interface target, of another underlying type (Perennial's
`errors.As.spec` allows any result). Go's `As` (`errors/wrap.go`) walks `err`'s tree: `err` is not
assignable to the target's element type, it has no `As` method, and no `Unwrap` method ends the walk
with `false`, the target not written. Approved by etcd-grove-81 (2026-11-15) after an independent
review; the reasoning and the Go evidence are in `Spec/errors/AsLeafTy.lean`'s header.
-/
module

public import Spec.errors.AsLeafTy

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

axiom errors.AsLeafTy.wp_proof : errors.AsLeafTy.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
