/-
The trust boundary: **a context with no values has no outgoing metadata** (grpc's `metadata` is
names-only; `notes/authkv-main-plan.md`, round 1, F-W4, 2026-10-29). Lean-first (no Rocq
counterpart).

`outgoingOf` (`Outgoing.lean`) is opaque: the model says nothing of a context's outgoing metadata
but what `AppendToOutgoingContext` adds. grpc reads it as the value of the context at its own
unexported key (`FromOutgoingContext`: `ctx.Value(mdOutgoingKey{})`, `(nil, false)` when absent).
A context whose descriptor has no values (`isContext ci cd`, `cd.Values = ∅`: Perennial's
`Value(k)` of it returns nil at every key, so at grpc's) therefore has none. `context.WithTimeout`
of `Background()` gives such a descriptor (Perennial's `bgDeadlineDesc`); `examples/authkv`'s
`anon` relies on it (its calls carry no token).
-/
module

public import Proof.google_golang_org.grpc.metadata.Outgoing
public import Perennial.Proof.context

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
variable [package_sem : context.Assumptions]

/-- **A context with no values has no outgoing metadata** (see the file header). -/
axiom metadata.outgoingOf_noValues (ci : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) :
    context.isContext ci cd ⊢ ⌜cd.Values = ∅ → metadata.outgoingOf (GoInterface.ok ci) = none⌝

end proof

end EtcdGrove
end Perennial
