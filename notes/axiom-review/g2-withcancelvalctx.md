# `context.WithCancelValCtx.wp_proof` (G2's (h): keeps `outgoingOf`): survives

**Reviewed** 2026-10-30, at `g2-stmts` `7ec9f1f715` (diff against `8527537fba`; etcd fork
`249d76bea`, grpc v1.84.0, go1.27.3), by the `axiom` skill. Branch `axiom/g2-withcancelvalctx` (deleted 2026-10-30; last commit `8b47c519de`).

## The axiom

`context.WithCancelValCtx.wp_proof` (`Proof/context/WithCancelValCtx.lean`, triple in
`Spec/context/WithCancelValCtx.lean`): `context.WithCancel(&valCtx{inctx})`
(`client/v3/watch.go:282`, `newWatcherGRPCStream`), under `isPkgInit context ∗ isPkgInit clientv3 ∗
p ↦□ valCtx.mk (interface.ok inctx) ∗ context.isContext inctx cs`, returns `(ok ctx', cancel)` with

1. `cancelSpec cancel γ' True` (cancel from anywhere);
2. `isContext ctx' { Values := ∅, Deadline := none, Done_gn := γ', PDone := True }`;
3. new in G2: `⌜metadata.outgoingOf (ok ctx') = metadata.outgoingOf (ok inctx)⌝`.

The commit's diff changes only conjunct 3 (and the import of `metadata/Outgoing.lean`); 1 and 2 were
reviewed before (`notes/audit.md`, the `context` row: ok). Reviewed with it: `metadata.outgoingOf`
(opaque; its docstring's reading, sharpened in the same commit: `FromOutgoingContext`'s view, keys
lower-cased, no raw `MD` with keys colliding up to case), `mdAdd`/`mdSet`;
`metadata.AppendToOutgoingContext.wp_proof`, `FromOutgoingContext.wp_proof`, `withVersion.spec`,
`context.WithTimeoutBackgroundMd.wp_proof` (`outgoingOf ctx' = none`),
`clientv3.streamKeyFromCtx.wp_proof` (returns `streamKeyOf (outgoingOf ctx)`: the one spec that lets
a program *observe* `outgoingOf`) with `streamKeyOf_none`/`streamKeyOf_single`, grpc's attempt
contract (`grpcAttemptMd`, `InvGrpc.lean:896-904`; `clientAttemptMdOf`, `InvKVConn.lean:775`), the
other `Spec/context/WithCancel*.lean`, and Perennial's `isContextDef`
(`Perennial/Proof/context/Base.lean:481`).

## Verdict: survives

Claim 3 is true of Go for every `inctx` the precondition admits, and it is consistent with every
other axiom over `outgoingOf`. No counterexample.

The Go facts (go1.27.3 `src/context/context.go`; grpc v1.84.0 `metadata/metadata.go`; etcd
`client/v3/watch.go`):

- `valCtx` is `struct{ context.Context }` with its own `Deadline`, `Done` (the never-closed
  `valCtxCh`) and `Err` (`watch.go:275-279`); `Value` is the embedded `inctx`'s (promotion). It has
  no other methods, so it is never an `afterFuncer`.
- `WithCancel(parent)` (`context.go:241`) is `withCancel`: a fresh `&cancelCtx{}` and
  `propagateCancel(parent, c)` (`:476`), whose first statement is `c.Context = parent`. With
  `valCtx`'s `Done()` non-nil and open, and `parentCancelCtx` (`:383`) failing (whatever
  `inctx.Value(&cancelCtxKey)` returns, its `done` is not `valCtxCh`), and no `afterFuncer`, it takes
  the goroutine branch: `c.Context` stays `&valCtx{inctx}` (only the `afterFuncer` branch rewrites
  it, to a `stopCtx` whose `Value` would still be the parent's). `cancel` (`removeChild`) never
  writes `c.Context`.
- `(*cancelCtx).Value(key)` (`:442`) returns `c` at `&cancelCtxKey`, else `value(c.Context, key)`
  (`:776`): `&valCtx{..}` falls into `default`, `c.Value(key)`, i.e. `inctx.Value(key)`.
- grpc reads outgoing metadata only by `ctx.Value(mdOutgoingKey{})` (`FromOutgoingContext`
  `metadata.go:331`, `fromOutgoingContextRaw` `:319`, used by `stream.go:322` and
  `http2_client.go:579`), a key distinct from `&cancelCtxKey`. So `ctx'` and `inctx` yield the
  *same* `rawMD` (`md` and `added`), before and after either is cancelled, and every function of it
  (`FromOutgoingContext`'s merge, the transport's headers, `streamKeyFromCtx`) agrees.

`examples/axiomcx/withcancelvalctx/probe_test.go` (this branch) records it: `GOTOOLCHAIN=go1.27.3 go
test -count=1 -v ./axiomcx/withcancelvalctx/` in `examples/`, all six tests pass:

- `TestKeepsOutgoing`: for eleven parents (`Background`, `TODO`, one and two appends with a
  mixed-case key, `NewOutgoingContext(Pairs(..))` plus an append, an empty `MD{}`, a cancelled
  `*cancelCtx` over metadata, metadata over a cancelled context, an expired `*timerCtx` over
  metadata, a nested `WithCancel(&valCtx{..})`, `WithoutCancel`), `FromOutgoingContext` and
  `streamKeyFromCtx` of the result equal the parent's, before and after `cancel`; the result is a
  `*context.cancelCtx`, live, with no deadline;
- `TestEmptyIsSome`: an empty raw `MD` stays `(MD{}, true)`, not "none";
- `TestThroughWatcher`: through the real path (`clientv3.NewWatchFromWatchClient` with a fake
  `WatchClient`): the context `openWatchClient` passes to `Watch` is a `*context.cancelCtx` carrying
  the caller's `{authorization:[tok] k:[v]}`, and stays live after the caller's context is cancelled;
- `TestNilParent`, `TestNotAfterFuncer`, `TestCollidingKeysMargin`: attacks 1, 5 and 6 below.

## Attacks tried

1. **A nil or nil-backed `inctx`.** `WithCancel(&valCtx{nil})` panics, in `WithCancel` itself:
   `parentCancelCtx` calls `valCtx.Value(&cancelCtxKey)`, promoted to a nil interface
   (`TestNilParent`). The spec excludes it twice: `interface.ok inctx` is a non-nil interface, and
   `isContext inctx _`'s `#HValue` promises exactly that `Value(&cancelCtxKey)` returns. (This is
   about the pre-existing conjuncts 1-2, not 3; noted because the review was asked about nil.) A
   typed-nil pointer inside `inctx` cannot meet `#HValue` either. Fails.
2. **A cancelled or expired `inctx`.** `valCtx` hides its `Done`/`Err`/`Deadline`, never its `Value`;
   cancellation writes `err`/`done`/`cause`, never a value. Equality holds (test). Fails.
3. **Inconsistency with the other `outgoingOf` axioms** (the attack that refuted
   `outgoingOf_noValues`). The facts the logic has: Append (`outgoingOf c' = mdAdd (outgoingOf ctx)
   k v`), `withVersion` (`mdSet ..`), `WithTimeoutBackgroundMd` (`= none`), and this one; each about
   a fresh existential result, plus `streamKeyFromCtx`'s return value. To derive `False` a proof
   needs two of these results equated, or this result equated with a value whose `outgoingOf` is
   fixed otherwise. No spec returns its argument or equates two contexts (`GenericClientStream.Context`
   only delegates to the inner stream's method); `ctx'` is a fresh `*cancelCtx` in Go (distinct type
   from Append's/`withVersion`'s `*valueCtx` and from `WithTimeout`'s `*timerCtx`, and a distinct
   location). Instantiating with `inctx := Append(..)` or `inctx := withVersion(..)` gives
   `outgoingOf ctx' = mdAdd ..`/`mdSet ..`, both what Go returns; chaining (`inctx` itself a
   `WithCancelValCtx` result) composes by transitivity, as in Go (`nested-valCtx`). The refuted law
   over `isContext`'s `Values` is gone (`OutgoingNoValues.lean` deleted), and `Values := ∅` in
   conjunct 2 constrains nothing (`isContextDef` never reads `Values`). Fails.
4. **An observer that disagrees.** The ways the logic reads `outgoingOf` back: `streamKeyFromCtx`
   (a program can compare `streamKeyFromCtx(ctx')` with `streamKeyFromCtx(inctx)`, or with a
   literal; the first is equal in Go, the second needs `outgoingOf` of a base context no spec fixes
   except `WithTimeoutBackgroundMd`'s `none`, also true of Go) and grpc's attempt contract (the
   handler sees the credentials' values then `outgoingOf ctx`'s: for `w.ctx = ctx'` that is
   `inctx`'s metadata, which is what grpc-go sends, `TestThroughWatcher`). `FromOutgoingContext`'s
   spec gives no contents. No Go program makes `ctx'` and `inctx` read differently. Fails.
5. **`propagateCancel`'s other branches** rewriting `c.Context` (the `afterFuncer` branch wraps the
   parent in a `stopCtx`). `valCtx` has only `Context`'s four methods (`TestNotAfterFuncer`); even
   the `stopCtx` would delegate `Value` to its parent. Fails.
6. **The colliding-keys margin of `outgoingOf`'s reading.** For a raw `MD` with keys equal up to
   case (`NewOutgoingContext(ctx, MD{"K": .., "k": ..})`), `FromOutgoingContext` depends on map
   iteration, so two reads of the *same* `inctx` differ (`TestCollidingKeysMargin`: both keys seen in
   1000 reads, for `inctx` and for `ctx'` alike). A program comparing `streamKeyFromCtx(ctx')` with
   `streamKeyFromCtx(inctx)` would then panic sometimes while the axioms prove it does not; but the
   same holds of two `streamKeyFromCtx(inctx)` calls, so the fault is the margin of
   `streamKeyFromCtx.wp_proof`/`outgoingOf` (documented in both docstrings), not of (h). Not
   provable either way: no spec here builds such a context (`NewOutgoingContext` has no spec;
   `AppendToOutgoingContext`, `Pairs`, `MD.Set` lower-case keys). Fails for (h); the margin stays as
   recorded.
7. **Cross-execution reading of `outgoingOf`** (one fixed function of a pointer value, while the
   allocator may put contexts with different metadata at the same location in different runs).
   Shared by every `outgoingOf` axiom whose result is a fresh context (Append, `withVersion`,
   `WithTimeoutBackgroundMd`), recorded in `withtimeout-outgoing.md`, "Remarks"; no proof relates
   two executions. Not specific to (h).
8. **Conjuncts 1 and 2.** Unchanged by the diff; reviewed earlier (`notes/audit.md`). Not re-attacked
   beyond attack 1.

## Remarks (not refutations)

- **Layering.** The spec now imports `Proof/google_golang_org/grpc/metadata/Outgoing.lean` into a
  `context` spec (`notes/g2-watch-auth.md`, "(h) makes a context spec depend on grpc"). Not a
  soundness matter: the conjunct is a fact about grpc's view of the context, and the true general
  statement is grpc-free (a `*cancelCtx` delegates `Value` at every key but `&cancelCtxKey`), from
  which (h) would follow for any `Value`-defined view. That is the Perennial proposal already in
  `notes/perennial-changes.md` ("Context model: `WithCancel` keeps its parent's values"); when it
  lands, (h)'s conjunct 3 becomes provable from it plus a law "`outgoingOf` is a function of
  `Value(mdOutgoingKey{})`", and the import goes.
- The docstring's "Consistent with the other axioms over `outgoingOf` by the convention ..." is
  accurate (attack 3); the claim does not rest on freshness, only on no spec equating two contexts.

## What rests on it

`etc/tcb-collections/{cache-client,cachekv,client,linkv3p,watch,watchkv}.txt` list it; it is used by
`watcher.newWatcherGRPCStream.wp_proof` (`Proof/go_etcd_io/etcd/client/v3/Link.lean:1100`), and the
new conjunct only by the G2 watch-with-auth chain (`newWatcherGRPCStream`'s post `outgoingOf w.ctx =
outgoingOf inctx`, `watchCheckOk`'s `m`). (`etc/tcb-report.py --roots` not run: no Lean file changed.)

## Proposed restatement

None needed.
