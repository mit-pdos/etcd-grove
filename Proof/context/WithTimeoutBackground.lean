/-
The trust boundary: `context.WithTimeout(context.Background(), d)` (an axiom again since 2026-10-29,
for one conjunct). Everything but the outgoing metadata is Perennial's `wp_WithTimeout_Background`
(`Perennial/Proof/context/WithDeadlineBackground.lean`, proved; this file proved the spec from it
2026-10-23..29, `notes/client-timeouts-plan.md` T3). The spec now also says the new context has no
outgoing grpc metadata, which nothing in Perennial's context model can say: `isContext` does not
constrain a descriptor's `Values` (unused), and this repository's `metadata.outgoingOf` is opaque.
It is true in Go: the result is a fresh `*timerCtx` whose parent is `Background()`, and
`metadata.FromOutgoingContext` looks up grpc's own key with `Value`, which neither has. A first
attempt, a law that a context with no `Values` has no outgoing metadata, was inconsistent with
`AppendToOutgoingContext`'s axiom (`notes/axiom-review/outgoingOf-noValues.md`, branch
`axiom/outgoingOf-noValues`). The general fix, a Perennial `isContext` whose `Values` are what
`Value` returns, is in `notes/perennial-changes.md`; with it this is proved again.
-/
module

public import Spec.context.WithTimeoutBackground

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

/-- See the file header. -/
axiom context.WithTimeoutBackground.wp_proof :
    context.WithTimeoutBackground.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
