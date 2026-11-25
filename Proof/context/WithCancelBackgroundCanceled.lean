/-
**`WithCancel(Background())` with `Err() = Canceled` after `cancel()`: an interim axiom**
(`Spec/context/WithCancelBackground.lean`, `spec_canceled`). Interim, retired by the Perennial pin bump
past the change proposed in `notes/perennial-changes.md` ("`context.WithCancel`'s `cancel` does not say
`Err()` returns `Canceled`"): Perennial's `cancelCtx` invariant records a set error only as
`Canceled`'s or `DeadlineExceeded`'s value (`isCtxErr`), so `wp_WithCancel_gen` cannot give which; the
change keeps `Canceled` for a context cancelled by its own `cancel()` under a never-done parent, and
proves this statement unchanged. What gRPC's robustness driver's `ctx-canceled` section needs
(grpc's `toRPCErr` maps `context.Canceled` to `codes.Canceled`). Lean-first (no Rocq counterpart).
-/
module

public import Spec.context.WithCancelBackground

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : context.Assumptions]

/-- See the file header. Interim, retired by the Perennial pin bump past the change of
`notes/perennial-changes.md`, "`context.WithCancel`'s `cancel` does not say `Err()` returns
`Canceled`". -/
axiom context.WithCancelBackground.wp_proof_canceled :
  context.WithCancelBackground.spec_canceled (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
