# `context.WithTimeoutBackground.wp_proof` (with its outgoing-metadata conjunct): survives

**Reviewed** 2026-10-29, at `authkv-main-skel` `a0eb0d94fd` (Perennial pinned there, grpc v1.84.0,
go1.27.3), by the `axiom` skill. Branch `axiom/withtimeout-outgoing`.

## The axiom

`context.WithTimeoutBackground.wp_proof` (`Proof/context/WithTimeoutBackground.lean`, triple in
`Spec/context/WithTimeoutBackground.lean`): `WithTimeout(ok backgroundCtxVal, d)`, for every `d`,
under `isPkgInit context ∗ isClosedchanInit`, returns `(ok ctx', cancel)` with

1. `cancel` callable any number of times from anywhere (`□ ∀ Φ, ... WP cancel #() {{ Φ }}`);
2. `context.isContext ctx' cd` for some descriptor `cd`;
3. new: `⌜metadata.outgoingOf (GoInterface.ok ctx') = none⌝`.

Until `a0eb0d94fd` the spec (with `⌜cd.Values = ∅⌝` in place of 3) was proved from Perennial's
`wp_WithTimeout_Background` (`Perennial/Proof/context/WithDeadlineBackground.lean:214`), whose post
is `isContext ctx' (bgDeadlineDesc d γ')` and the same `cancel` triple; the diff of that commit
changes only the last conjunct, so 1 and 2 are Perennial's proved facts, weakened (`cd`
existential, an extra unused premise). The only new claim is 3.

Reviewed with it: `metadata.outgoingOf` (opaque, `Outgoing.lean`), `mdAdd`/`mdSet`;
`metadata.AppendToOutgoingContext.wp_proof`, `metadata.FromOutgoingContext.wp_proof`;
`withVersion.spec` (`client/v3`, the other spec stating `outgoingOf`); grpc's attempt contract
(`grpcAttemptMd`, `InvGrpc.lean:881`, the one consumer of `outgoingOf` for any context);
authkv's `deliversOutgoing` (`ClientAuth.lean:97`, a hypothesis, not an axiom); every spec of
`Spec/context/` (`Err`, `ErrAny`, `ErrDone`, `TODO`, `ValueKeepAlive`, `ValueStartTime`,
`WithCancelBackground`, `WithCancelTodo`, `WithCancelValCtx`, `WithValue`) and `WithRequireLeader`.

## Verdict: survives

Claim 3 is true of Go, and no spec in the repository constrains `outgoingOf` of the value the call
returns in a way that contradicts it. No counterexample.

The Go facts (`$GOROOT/src/context/context.go` of go1.27.3; grpc v1.84.0 `metadata/metadata.go`):

- `WithTimeout(parent, d)` is `WithDeadline(parent, time.Now().Add(d))`, `WithDeadlineCause`
  (`context.go:633`): `Background()`'s `Deadline()` is `ok = false`, so the `WithCancel(parent)`
  branch is never taken, and the result is always a freshly allocated `&timerCtx{...}` (returned on
  both the expired, `dur <= 0`, and the timer path).
- `timerCtx` embeds `cancelCtx`, whose `Value` (`context.go:442`) returns itself at
  `&cancelCtxKey` and otherwise `value(c.Context, key)`: the parent's, `Background()`'s, `emptyCtx`'s
  `Value` (`context.go:196`), `nil` at every key. `cancel` writes `err`/`done`/`cause`, never the
  parent or a value: the answer is the same before and after.
- `FromOutgoingContext` (`metadata.go:331`) is `ctx.Value(mdOutgoingKey{}).(rawMD)`: `nil`, so
  `(nil, false)`; grpc's transport reads the same key. "No outgoing metadata" is the right reading
  of `none` (not `some` of an empty map, which `NewOutgoingContext(ctx, MD{})` would give).

`examples/axiomcx/withtimeoutoutgoing/probe_test.go` (on this branch) records these: run with
`GOTOOLCHAIN=go1.27.3 go test -count=1 -v ./axiomcx/withtimeoutoutgoing/` in `examples/`, all
four tests pass (no metadata for `d` in `{-1h, 0, 1ns, 1h}`, before and after `cancel`, dynamic
type `*context.timerCtx`; two calls unequal; `Background()` has none and is one value; a
`*timerCtx` over a parent with metadata does carry it).

## Attacks tried

1. **Inconsistency with `AppendToOutgoingContext` (the attack that refuted `outgoingOf_noValues`).**
   That axiom was a law over every `isContext` descriptor; this one is a fact about the value one
   call returns, and the only facts the logic has about that value are this post. To get `False`
   with Append's `outgoingOf c' = mdAdd .. = some _` the proof would need `c' = ok ctx'`. Append's
   `ci` and `ctx'` are both existentials chosen by the axioms, never equated by any spec; in Go
   `ci` is a fresh `*valueCtx` (`context.WithValue`), a different dynamic type
   (`GoInterfaceOk` carries the `go.GoType`, `PointerType valueCtx.ty` vs `PointerType
   timerCtx.ty`) and a different location. Appending over `ctx'` (`Append(ok ctx', ..)`) gives
   `mdAdd none k v` for the child, consistent with Go, and changes nothing about `ctx'`. Fails.
2. **A context spec returning a value equal to, or aliasing, `ctx'`.** Every context spec returns
   a fresh existential (`WithCancel*`, `WithValue`, `withVersion`, `WithRequireLeader`) or a
   fixed value of another type (`TODO()`'s `todoCtxVal`); none returns its argument, and none
   states `outgoingOf` of its result but Append (`mdAdd`, always `some`) and `withVersion`
   (`mdSet`, always `some`), both of a fresh `valueCtx`. `WithValue`'s post equates `incomingOf`
   of child and parent, not `outgoingOf`. No spec gives an equation `x = ok ctx'` with `outgoingOf
   x ≠ none`. Fails.
3. **`Background()` carrying outgoing metadata.** No spec states `outgoingOf (ok
   backgroundCtxVal)` at all; in Go it has none (`emptyCtx.Value` is `nil`), and every
   `Background()` is the same value `backgroundCtx{}` (so a fact about one is about all: there is
   none to contradict). Append over `Background()` returns a new `valueCtx`, not
   `backgroundCtxVal`. Fails.
4. **Two calls returning equal values.** The post would give `none` for both, so equality would
   not contradict anything; in Go they are distinct (`c1 != c2`, test). Perennial's model allocates
   the `timerCtx` (translated `WithDeadlineCause`), so the values are distinct locations. Fails
   (and harmless).
5. **An observer that reads the metadata back and panics on disagreement.** The logic sees
   `outgoingOf` through `grpcAttemptMd` (a handler sees, on keys grpc does not set, the credentials'
   values then `outgoingOf ctx`'s) and authkv's `deliversOutgoing` (a hypothesis of
   `Results.lean`'s lemma, not an axiom). With `none`, the handler sees the credentials' values
   only: that is what grpc-go sends for a context with no `mdOutgoingKey{}` value.
   `FromOutgoingContext`'s spec gives no contents, so the client cannot observe it locally. A Go
   program that disagrees would need a `WithTimeout(Background())` context that carries metadata,
   which Go never makes. Fails.
6. **The `d` boundary** (negative, zero, overflow of `Now().Add(d)`): only the timer path
   changes; the result is a `*timerCtx` over `Background()` in every case (test). Fails.
7. **The parts 1 and 2** (cancel from anywhere, no panic): Perennial's proved lemma, the axiom
   weaker (existential `cd`, the extra `isClosedchanInit` premise unused). Not re-attacked beyond
   checking the commit's diff touches only conjunct 3.

## Remarks (not refutations)

- **Why the triple form is the right shape.** A pure law over the dynamic type ("every
  `*timerCtx` has no outgoing metadata", or `outgoingOf (ok ⟨PointerType timerCtx.ty, #l⟩) =
  none`) would be false: `WithTimeout(AppendToOutgoingContext(Background(), "k", "v"), d)` is a
  `*timerCtx` that carries `k` (`TestTimerOverMetadata`), and grpc's attempt contract would then
  claim the handler sees none of it. Tying the fact to the call, as this axiom does, is what makes
  it true. Keep it in this form until Perennial's `isContext` ties `ContextDesc.Values` to `Value`
  (`notes/perennial-changes.md`), from which it would be proved.
- **`outgoingOf` is a pure function of a pointer value** (as `incomingOf`). Within one execution
  a context pointer determines its context, and every equation the proofs use is obtained in the
  current execution; but across executions the same location can be a `WithTimeout(Background())`
  result in one and a `WithTimeout` of a context with metadata in another, so the axioms here are
  true of the honest reading of `outgoingOf` only per execution, not of one fixed function. No
  proof can exploit this (it never relates two executions; every attack above lives in one), and
  it is the same for `AppendToOutgoingContext`'s and `withVersion`'s `valueCtx` results, so it is
  not specific to this axiom. A persistent ghost assertion ("the context `c` carries the outgoing
  metadata `md`", made where the context is) would state it without the convention; worth doing if
  `outgoingOf` grows more laws.

## What rests on it

The whole spec is used by every client example and the read loop (`grep
WithTimeoutBackground.wp_proof`: `common`, `linkv3p`, `linkvtxn`, `authkv`, `putget*` links,
`etcdserver/read/Link.lean`); conjunct 3 only by `authkv.reqCtx.wp_proof` and
`client.wp_WithTimeout_bg` (`TimeoutCtx.lean:56`), and through them authkv's results.
(`etc/tcb-report.py --roots` not run: no Lean file changed, and it needs an up-to-date full build.)

## Proposed restatement

None needed. The docstring of `Proof/context/WithTimeoutBackground.lean` could cite this review.
