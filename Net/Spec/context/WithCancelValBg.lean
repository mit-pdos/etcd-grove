/-
**Interim pending hypothesis** (not an axiom: a hypothesis of the linked results that use it, until
its retirement below; approved as interim on #24, 2026-11-24, subject to an adversarial review).

`context.WithCancel(parent)` (go1.27.3 `src/context/context.go`) for a `parent` that is `Background()`
or a chain of `*valueCtx`s over it (`context.ctxBg`, `Net/Proof/context/CtxBg.lean`: what
`WithValue` builds, `context.WithValue.specPtr`). `withCancel` makes a fresh `*cancelCtx` `c` and
calls `c.propagateCancel(parent, c)`, which sets `c.Context = parent` and returns at once, since
`parent.Done()` is `nil` (each `*valueCtx` promotes its parent's `Done`, and `Background()`'s is
`nil`): `c` registers with no parent and no goroutine is started. So the result is what
`WithCancel(Background())` gives (Perennial's `wp_WithCancel_Background`, with `PDone' := True`): a
`*cancelCtx` (`isCancelCtxCtx`) with no deadline (`Deadline()` reaches `Background()`'s through the
chain), done only by its cancel function, which needs nothing (`cancelSpec … True`: `c.cancel(true,
Canceled, nil)`, whose `removeChild(parent, c)` returns at `parentCancelCtx`'s `Done() == nil`). The
post states less than Go does (nothing of `Value` on other keys). `Values := ∅` claims nothing: no
context predicate reads a descriptor's `Values` (`isContext` specifies `Value` only at
`&cancelCtxKey`); it is sound only while that stays true.

Evidence (go1.27.3, `examples/stdlib/ctxhyp/`, `GOTOOLCHAIN=go1.27.3 go test -race ./stdlib/ctxhyp/` in
`examples/`): `TestWithCancelValBg` (chains of 0 to 8 `*valueCtx`s over `Background()`, keys net/http's
context keys, strings, ints, pointers, `struct{}{}`: the chain's `Done()` is `nil`; the result is a
`*context.cancelCtx` whose `Context` is the chain; no goroutine started; `Deadline()` is
`(time.Time{}, false)`; `Done()` open and `Err()` nil until cancel; a child `WithCancel` of it registers
without a goroutine and is canceled with it; cancel twice is fine; then `Done()` closed, the same
channel, `Err()` is `Canceled`; the chain unchanged and not done), `TestNetHTTPChain` (`conn.serve`'s
own chain: `WithCancel(WithValue(WithValue(Background(), ServerContextKey, s), LocalAddrContextKey,
la))`); the adversarial review's (`notes/axiom-review/context-interim-hypotheses.md`: sound, no
counterexample) `TestWithCancelChainConcurrent` (under `-race`: concurrent cancel, `Done`, `Err`,
`Deadline`, `Cause`; children `WithCancel`, `WithTimeout`, `AfterFunc`), `TestWithCancelChainSequential`,
`TestDeepChain` (depth 100000).

**Why a hypothesis.** Perennial's `WithCancel` specs take a parent that satisfies `isParentCtx`
(`Background()`, `TODO()` or an `isContext`); a `*valueCtx` chain over `Background()` is none of them
(its `Done()` is `nil`, which no `isContextDone` describes). **Retired by** Perennial's `isParentCtx`
widened to such chains (with `WithValue`'s spec giving `ctxBg`), and this triple proved from
`wp_WithCancel_gen` (`notes/perennial-changes.md`, the same entry as `WithValue`'s).
-/
module

public import Net.Proof.context.CtxBg

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [package_sem : context.Assumptions]

/-- See the file header. -/
abbrev context.WithCancel.specValBg : Prop :=
  ∀ (parent : GoInterfaceOk),
  {{ isPkgInit (PROP := IProp GF) pkg_id.context ∗ context.ctxBg parent }}
    (App (Val (@! context.WithCancel)) (Val #(GoInterface.ok parent)))
  {{ (ctx' : GoInterfaceOk) (γ' : context.ContextNames) (cancel : GoFunc),
      RET (PairV #(interface.ok ctx') #cancel);
      context.cancelSpec cancel γ' iprop(True) ∗
      context.isContext ctx' { Values := ∅, Deadline := none, Done_gn := γ', PDone := iprop(True) } ∗
      context.isCancelCtxCtx ctx'
        { Values := ∅, Deadline := none, Done_gn := γ', PDone := iprop(True) } }}

end spec

end Perennial
