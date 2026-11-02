# `metadata.outgoingOf_noValues`: refuted (inconsistent with `AppendToOutgoingContext`)

**Reviewed** 2026-10-29, at `authkv-main-skel` `c54efdd0b1` (Perennial `ad74ee4f6`, grpc v1.84.0,
go1.27.3), by the `axiom` skill. Branch `axiom/outgoingOf-noValues`.

## The axioms

- `metadata.outgoingOf_noValues` (`Proof/google_golang_org/grpc/metadata/OutgoingNoValues.lean`):
  `context.isContext ci cd ⊢ ⌜cd.Values = ∅ → metadata.outgoingOf (GoInterface.ok ci) = none⌝`.
- with `metadata.outgoingOf` (opaque), `mdAdd`, `mdNorm` (`Outgoing.lean`);
- `metadata.AppendToOutgoingContext.wp_proof` (its result `c' = ok ci` has
  `isContext ci { cd with Values := vs }` and `outgoingOf c' = mdAdd (outgoingOf ctx) k v`);
- `metadata.FromOutgoingContext.wp_proof` (says nothing of `outgoingOf`);
- Perennial's context model: `context.isContext`/`isContextDef`, `ContextDesc.Values`
  (`Perennial/Proof/context/Base.lean`).

## Verdict: refuted, and the axiom is inconsistent with `AppendToOutgoingContext.wp_proof`

The claim the axiom makes is "a context whose descriptor has no values has no outgoing metadata",
and its docstring argues it from "Perennial's `Value(k)` of it returns nil at every key". That is not
what `isContext` says. `isContextDef` (`Base.lean:481`) never mentions `s.Values`: its `"#HValue"`
specifies `Value` only at `&cancelCtxKey`, and its docstring (`Base.lean:528`) says outright "the
`Values` field of `ContextDesc` is unused". `isContextDone` reads only `Done_gn` and `PDone`
(`isContextDone_congr`). So, for every context,

    isContext c s ⊢ isContext c { s with Values := ∅ }        (isContext_values_empty, 4 lines)

and the axiom becomes: **no context the model has an `isContext` for has outgoing metadata.**
`AppendToOutgoingContext`'s spec returns a context with an `isContext` and
`outgoingOf c' = mdAdd _ k v = some _`, so the two together give `False` after any append.

### The counterexample

`examples/axiomcx/outgoingnv/outgoingnv.go`:

```go
func Run() {
	ctx, cancel := context.WithCancel(context.Background())
	ctx2 := metadata.AppendToOutgoingContext(ctx, "k", "v")
	_, ok := metadata.FromOutgoingContext(ctx2)
	cancel()
	if ok {
		panic("outgoingnv: the appended context carries outgoing metadata")
	}
}
```

Go (`GOTOOLCHAIN=go1.27.3 go test -count=1 -v ./axiomcx/outgoingnv/` in `examples/`, grpc v1.84.0):

```
=== RUN   TestRunPanics
    outgoingnv_test.go:12: Run panicked: outgoingnv: the appended context carries outgoing metadata
--- PASS: TestRunPanics (0.00s)
```

(`AppendToOutgoingContext` is `context.WithValue(ctx, mdOutgoingKey{}, rawMD{...})`,
`metadata.go:250-263`; `FromOutgoingContext` returns `ok` for it, `metadata.go:331-335`.)

The proof, `Proof/github_com/mit_pdos/etcd_grove/examples/axiomcx/outgoingnv/Run.lean`:
`Run.wp_proof` proves `{{ isPkgInit outgoingnv }} Run #() {{ RET #(); True }}` from the two
reviewed axioms taken as hypotheses (Perennial's proved `wp_Background`, `wp_WithCancel_Background`,
`wp_slice_literal` for the rest); after the append it rewrites the descriptor's values away
(`isContext_values_empty`), applies the axiom, and closes the goal by `mdAdd _ _ _ ≠ none`, never
reaching `FromOutgoingContext` or the `panic`. `Run.wp_axioms` instantiates the hypotheses with the
axioms. `#print axioms`:

- `Run.wp_proof`: `propext, Classical.choice, Quot.sound` and Perennial's generic type axioms
  (`sync.Map`, `sync.poolChainElt`, `internal.synctest.*` and their `underlying`/`zero_val`), which
  every proof importing the prelude prints; no `sorry`;
- `Run.wp_axioms`: the same plus exactly `metadata.outgoingOf_noValues` and
  `metadata.AppendToOutgoingContext.wp_proof`.

Translated as the temporary Goose project `axiomcx-outgoingnv` (`etc/goose.py`, on this branch only).

### A second witness: the repository's own context axioms

Even without the congruence lemma, specs here hand out `Values := ∅` descriptors for contexts that do
carry outgoing metadata in Go: `WithRequireLeader.wp_proof` (`client/v3`) gives
`WithCancel(WithRequireLeader(Background()))` the descriptor `{ Values := ∅, .. }`, and in Go that
context's `Value(mdOutgoingKey{})` is `WithRequireLeader`'s `rawMD` (a `*cancelCtx` delegates `Value`
to its parent, `context.go:442`), so `FromOutgoingContext` returns `{hasleader: [true]}`. The axiom
says `outgoingOf` of it is `none`. No spec here observes the contents (FromOutgoingContext's spec
gives none), so this one is a false statement rather than a provable panic, but it shows the
descriptor's `Values` is not "the context's values" anywhere in the model (`WithCancelValCtx`,
`WithCancelTodo` and `newWatcherGRPCStream`'s contexts are other `Values := ∅` descriptors of
contexts that may carry the caller's metadata).

## Attacks tried

1. **A context with no values that grpc still treats as carrying outgoing metadata**: any context
   at all, since `Values` is unconstrained. Succeeded (above).
2. **A `valueCtx`/`cancelCtx` chain reported as `Values = ∅` while `Value(mdOutgoingKey{})` is
   non-nil**: `WithCancel` of `AppendToOutgoingContext`'s result (or of `WithRequireLeader`'s):
   `WithCancelGen`'s `wp_WithCancel_any` keeps the parent's descriptor, but the congruence lemma
   makes it moot. Gives the false statement of the second witness; the provable panic needs
   `outgoingOf ≠ none`, which only `AppendToOutgoingContext` supplies (attack 4).
3. **`NewOutgoingContext(ctx, MD{})`, some-empty against `none`**: no spec of `NewOutgoingContext`
   exists here (only `WithRequireLeader` and `withVersion` mention it, and `withVersion` states
   `mdSet`, which is `some`); Go's `FromOutgoingContext` returns `(MD{}, true)` for it while
   `outgoingOf = none` would mean "absent". Not exploitable without a spec that reads `outgoingOf`
   back; and `mdNorm` does not identify `none` with `some (fun _ => none)`, so where the auth proofs
   distinguish them (`ClientAuth.lean`, `cases ho : outgoingOf c`) the difference is real. Moot
   once the axiom is restated by provenance (below).
4. **With `AppendToOutgoingContext`'s `{ cd with Values := vs }`**: the false equation
   `mdAdd (outgoingOf ctx) k v = none`. This is the counterexample.

## What rests on it

Only `authkv.reqCtx.wp_proof` (`Proof/github_com/mit_pdos/etcd_grove/examples/authkv/reqCtx.lean:46`),
and through it authkv's `Link`/`Results`/`Main` (the closed authkv result). Its use is true in Go:
`reqCtx` applies the axiom to `context.WithTimeout(context.Background(), d)`, a fresh `*timerCtx`
over `Background()`, which has no `mdOutgoingKey{}` value. The fault is the statement's
generality, not authkv's need. (`etc/tcb-report.py --roots` not run: it needs a full `lake build`.)

## Proposed restatement (not applied)

State the fact by provenance, where it is true, instead of over `isContext`'s unconstrained
descriptor. Preferred: a trust-boundary triple of the one call authkv makes,

```lean
/-- `context.WithTimeout(context.Background(), d)` has no outgoing metadata: a fresh `*timerCtx`
over `Background()` (its `Value` delegates to `Background()`'s, which is nil at every key), so
grpc's `ctx.Value(mdOutgoingKey{})` is nil. -/
abbrev context.WithTimeoutBackgroundNoMD.spec : Prop :=
  ∀ d, {{ isPkgInit pkg_id.context ∗ context.isClosedchanInit }}
    WithTimeout (ok backgroundCtxVal) d
  {{ (ctx' cd cancel), RET (ctx', cancel);
      <cancel's spec> ∗ context.isContext ctx' cd ∗ ⌜metadata.outgoingOf (GoInterface.ok ctx') = none⌝ }}
```

(the existing `context.WithTimeoutBackground.spec` with the one conjunct; the `⌜cd.Values = ∅⌝`
conjunct can go, nothing else reads it). It is consistent with `AppendToOutgoingContext`: an
append's result is a fresh `*valueCtx`, never a fresh `*timerCtx` over `Background()`. Equivalent
alternatives: a pure axiom `metadata.outgoingOf_background : outgoingOf (ok backgroundCtxVal) = none`
plus a law that `WithCancel`/`WithTimeout` preserve `outgoingOf` (a `*cancelCtx`'s `Value` delegates
to its parent at every key but `&cancelCtxKey`), which would also serve `WithRequireLeader` and the
`valCtx` contexts. Either way, the descriptor's `Values` should not be used as evidence about
`Value` until Perennial's `isContext` ties them (a `"#HValue"` at every key `k ∉ dom Values`
returning nil: a Perennial change, `notes/perennial-changes.md`, if wanted).
