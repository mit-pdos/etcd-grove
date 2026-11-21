/-
The trust boundary: `errors.As` of an error in whose tree, to depth one, nothing matches the
target's element type (`nil`, a leaf, or a wrapper unwrapping once to `nil` or a leaf). Go's `As`
(`errors/wrap.go`) returns `false`, the target not written; the reasoning, the Go source lines and
the evidence are in `Spec/errors/AsNoMatch.lean`'s header and `notes/axiom-review/asnomatch.md`.
It replaces `errors.AsLeafTy` (its leaf case, `Proof/errors/AsLeafTy.lean`) and the four
`apierrors` checks' axioms (prove-k8s2, 2026-11-20).
-/
module

public import Spec.errors.AsNoMatch

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

axiom errors.AsNoMatch.wp_proof : errors.AsNoMatch.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
