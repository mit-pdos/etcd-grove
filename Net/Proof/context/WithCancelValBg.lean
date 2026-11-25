/-
`context.WithCancel` on a chain of `*valueCtx`s over `Background()`
(`Net/Spec/context/WithCancelValBg.lean`, `context.WithCancel.specValBg`), assumed.
-/
module

public import Net.Spec.context.WithCancelValBg

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [package_sem : context.Assumptions]

/-- **Trust-boundary axiom, interim** (until 2026-11-25 a hypothesis of the linked results that used
it; made an axiom on #18, 7144816148, option (a)): `context.WithCancel` meets
`context.WithCancel.specValBg` (the spec file's header: what Go does, and the evidence,
`examples/stdlib/ctxhyp/`). Perennial's `WithCancel` specs take an `isParentCtx` parent, which a
`*valueCtx` chain over `Background()` is not (its `Done()` is `nil`). Adversarially reviewed:
`notes/axiom-review/context-interim-hypotheses.md` (sound, no counterexample). **Retired by**
Perennial's `isParentCtx` widened to such chains (with `WithValue`'s spec giving `ctxBg`) and this
triple proved from `wp_WithCancel_gen` (`notes/perennial-changes.md`, the same entry as
`WithValue`'s). -/
axiom context.WithCancel.wp_proofValBg : context.WithCancel.specValBg (GF := GF) (hG := hG)

end proof

end Perennial
