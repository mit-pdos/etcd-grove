/-
The trust boundary: `context.WithCancel(&valCtx{inctx})` (etcd's never-done parent of the watch
client's stream context) returns a cancellable context and its `cancel` (Perennial proves
`WithCancel` for a `*cancelCtx`-chain parent only; see the spec's file). Since 2026-11-04 (W1 of
Q1 (b), `notes/k8s-compactor-plan.md`, the user's approval) for any `inctx` the watch takes
(`watchCtx`), not only a model one: `valCtx.Done()` is etcd's own `valCtxCh` and never reads
`inctx`, and `parentCancelCtx(&valCtx{inctx})` calls `inctx.Value(&cancelCtxKey)` (promoted; go1.27.3
`context.go:388`) and fails: that call returns (`watchCtx`'s `"#HCC"`), and a `*cancelCtx` it returns
is a valid one (`isCancelCtxAny`, not a typed nil, which `p.done.Load()` would dereference), whose
`done` is other than `valCtxCh`; so Go's `propagateCancel` takes the same goroutine branch; `inctx`
reaches the result only through `Value` (the outgoing metadata, `outgoingOf`).
(Corrected by the context sweep's fixes, 2026-11-13, decided by etcd-grove-81,
`notes/ctx-sweep-fixes.md`: until then `watchCtx` had no `"#HCC"` and this justification said
`parentCancelCtx` fails "whatever `inctx` is", overlooking the `Value` call; a context whose `Value`
panics at `&cancelCtxKey`, or answers a typed-nil `*cancelCtx`, met the premise and made `WithCancel`
panic, `examples/premisefix/watchctx`.)
-/
module

public import Spec.context.WithCancelValCtx

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

axiom context.WithCancelValCtx.wp_proof :
  context.WithCancelValCtx.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
