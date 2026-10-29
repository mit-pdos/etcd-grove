# `context.WithTimeoutBackgroundMd` (2026-10-29)

**Reviewed:** `context.WithTimeoutBackgroundMd.wp_proof` (`Proof/context/WithTimeoutBackgroundMd.lean`,
its triple `Spec/context/WithTimeoutBackgroundMd.lean`), at `189a0bfae4` of branch `auth-5b` (the
auth-mode merge's 5b). It is `context.WithTimeoutBackground.spec` (reviewed: `notes/audit.md`; since
2026-10-23 a theorem from Perennial's `wp_WithTimeout_Background`) plus the pure conjunct
`metadata.outgoingOf (GoInterface.ok ctx') = none`: the context `context.WithTimeout(context.Background(),
d)` returns carries no grpc outgoing metadata. Go: toolchain go1.27.3 (`GO_TOOLCHAIN`), grpc-go v1.84.0
(etcd's `client/v3/go.mod`), Perennial `ad74ee4f6`.

## Verdict

**Survives, with every attack tried.** No counterexample program was written (no gap found). The
conjunct is true of Go, consistent with every other axiom that constrains `outgoingOf`, and no axiom
lets a proof equate the returned context with a context that carries metadata. One caveat, not specific
to this axiom, is recorded below (`outgoingOf` as a function of values under nondeterministic
allocation).

## The claim against Go

- `WithTimeout(parent, d)` is `WithDeadline(parent, time.Now().Add(d))` (`context/context.go:704`);
  `WithDeadlineCause` (`:633`) returns `WithCancel(parent)` only if the parent has an earlier deadline
  (`Background()` has none, `:637`), else a fresh `&timerCtx{deadline: d}` (`:641`), including when
  `d <= 0` (cancelled at once, `:646-648`). So always a fresh `*timerCtx` whose parent is
  `backgroundCtx{}`.
- `metadata.FromOutgoingContext` (grpc `metadata/metadata.go:331`) and the transport
  (`FromOutgoingContextRaw`) read `ctx.Value(mdOutgoingKey{})`. `timerCtx`/`cancelCtx.Value` (`:442`)
  go to `value(c.Context, key)` (`:776`): `*timerCtx` → its parent; `backgroundCtx` → `nil` (`:801`). So
  no `rawMD`: `ok = false`, no metadata.
- Checked by running (go1.27.3, grpc v1.84.0, `d` ∈ {-1s, 0, 1ns, 1h}): the result is a
  `*context.timerCtx`, `FromOutgoingContext` returns `ok=false`, and `AppendToOutgoingContext` of it is a
  different value (`==` false).

## Attacks tried

1. **Equate the result with a context that has metadata.** `outgoingOf` is a function of the
   `GoInterface` value, so two calls returning equal values with different metadata would give `⊢
   False`. Every spec that produces an `outgoingOf` fact returns an existential context:
   `AppendToOutgoingContext` (`mdAdd …`, always `some`), `withVersion` (`mdSet …`, always `some`), this
   axiom (`none`); Perennial's `wp_WithTimeout_Background` also returns an existential `ctx'`. No spec
   returns its argument context unchanged or states an equality between contexts, and `isContext` is
   persistent and says nothing of identity. So a proof cannot derive `ctx' = c` for a `c` with
   metadata. The converse direction (proving the contexts differ, from `none ≠ some _`) is true of Go:
   `*timerCtx` vs a fresh `*valueCtx`, different types and allocations.
2. **A Go-level comparison.** `if ctxT == AppendToOutgoingContext(ctxT, k, v) { panic }`: the proof
   discharges the branch from `none ≠ some`; Go never takes it (checked). `if ctxT != … { panic }`: Go
   panics but the proof would need the equality, which nothing gives. Two `WithTimeout(Background())`
   results are both `none`: no conflict whatever their identity.
3. **Inconsistency (`⊢ False`).** The other constraints on `outgoingOf`: `AppendToOutgoingContext.spec`
   and `withVersion.spec` (results `*valueCtx`, metadata `some`), grpc's attempt contract
   (`grpcAttemptMd`, `InvGrpc.lean:884`; `clientAttemptMd`, `InvKVConn.lean:767`) and authkv's
   `reqCtx`/`setupCtx`/`ClientAuth` (consumers: they read `outgoingOf` of a given context, assert
   nothing new about a `WithTimeout(Background())` value). No two constrain the same value: the
   interpretation "the metadata Go's `FromOutgoingContext` finds" satisfies them all within an
   execution.
4. **Edge cases of `d`.** `d <= 0` and overflow of `Now().Add(d)` still return a `*timerCtx` over
   `Background()` (the earlier-deadline branch needs a parent deadline). No `WithCancel` path.
5. **What the consumers conclude.** `wp_WithTimeout_bgMd` (`TimeoutCtx.lean:86`) and `setupCtx`
   (`SetupInv.lean:248`) use it to conclude that an attempt of `SetUp`'s calls carries no token from
   the context: true of the Go client (`withVersion` adds only `client-api-version`).

## Caveat (not this axiom's alone)

`outgoingOf` is fixed before execution and is a function of the interface value `(type, loc)`, while
GooseLang's `AllocS` picks any fresh location. Across executions the same `(*timerCtx, l)` can be
`WithTimeout(Background())` in one and `WithTimeout(ctxWithMetadata)` in another, so no single function
matches Go's metadata in every execution; the same holds already for `AppendToOutgoingContext`'s
`(*valueCtx, l)` (and `incomingOf`). Within one execution locations are never reused, so the facts
the axioms give are jointly true of that execution, and no rule derives `outgoingOf` of a
`WithTimeout` over a non-`Background` parent (the attempt contract only reads it). Not exploitable by
a program as far as tried; a fully rigorous justification would tie `outgoingOf` to the heap (a ghost
map from contexts to metadata) rather than a global function. This axiom makes the fixed function
`none` on every `*timerCtx` location any `WithTimeout(Background())` could return.

## Not tried

A Lean proof of a program (none needed for a survival); closed-world contexts from outside the
program (a context from a library whose `Value` returns a `rawMD` at grpc's key): not reachable, as
the parent is `Background()` by the triple's syntax.
