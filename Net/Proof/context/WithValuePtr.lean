/-
`context.WithValue` on a pointer-typed key (`Net/Spec/context/WithValuePtr.lean`,
`context.WithValue.specPtr`), assumed.
-/
module

public import Net.Spec.context.WithValuePtr

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [package_sem : context.Assumptions]

/-- **Trust-boundary axiom, interim** (until 2026-11-25 a hypothesis of the linked results that used
it; made an axiom on #18, 7144816148, option (a)): `context.WithValue` meets
`context.WithValue.specPtr` (the spec file's header: what Go does, and the evidence,
`examples/stdlib/ctxhyp/`). Perennial translates `WithValue` names-only (`context.toml`:
`"!WithValue"`, for its `reflectlite.TypeOf(key).Comparable()`). Adversarially reviewed:
`notes/axiom-review/context-interim-hypotheses.md` (sound, no counterexample). **Retired by**
Perennial's `internal/reflectlite` model (reflection stage S0.5, Perennial branch `reflect-s05`):
`WithValue` translated with its body and this triple proved over it (`notes/perennial-changes.md`,
"`sync.NewCond.spec` does not say its result is not `nil`; `context.WithValue` names-only"). -/
axiom context.WithValue.wp_proofPtr : context.WithValue.specPtr (GF := GF) (hG := hG)

end proof

end Perennial
