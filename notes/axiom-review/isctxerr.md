# `errors.IsCtxErr` on a typed error with its own `Is`/`Unwrap` (axiom review, 2026-11-07)

**Reviewed** (lean at `ad87892323`; the sweep-plan review's BLOCKER): `errors.IsCtxErr.wp_proof`
(`Proof/errors/IsCtxErr.lean:29`, triple `Spec/errors/IsCtxErr.lean`). The Go code is go1.27.3's
`errors/wrap.go`, which is also the body Perennial translated, `@! errors.Is`.

## Repaired (premise fixes 6, part B, 2026-11-11)

The premise is now Perennial's `context.isCtxErr err`, a conjunct of the pre (`Spec/errors/IsCtxErr.lean`),
not `isTypedErr`. Unlike the plan below, `parseProposeCtxErr.spec` is unchanged (its pre already
gives `isCtxErr` through `isCtxErr_of_Canceled`/`_DeadlineExceeded`), and `watchServer.Watch`'s
first `errors.Is` (grpc's `Recv` error, not a context error) uses the proved `errors.Is.spec` over
`streamErr`'s tree. `notes/decisions.md`, "Premise fixes 6, part B"; Go test
`examples/premisefix/isctxerr`. The program below no longer meets the premises (`badUnwrap{}` is no
`isCtxErr`).

## Verdict

**Refuted (Go side). The Lean side has not been built yet.** The spec's only premise on `err` is
`context.isTypedErr err`, that is, its dynamic type has `Error() string`. Go's `errors.Is` runs
arbitrary user code: `is()` calls `err`'s own `Is` method (`wrap.go:59`) and its `Unwrap` method
(`:64`) once `err != target`. An error type whose `Is` or `Unwrap` panics meets the premise, and
`errors.Is` panics. The axiom also contradicts Perennial's own translated `errors.Is`, whose
`wp_Is` needs the error tree for exactly this reason. `notes/audit.md:295` already marked it
suspect.

## The program and its run

`examples/axiomcx/isctxerr/isctxerr.go`:

```go
type badUnwrap struct{}
func (badUnwrap) Error() string { return "" }
func (badUnwrap) Unwrap() error { panic("Unwrap") }

type badIs struct{}
func (badIs) Error() string        { return "" }
func (badIs) Is(target error) bool { panic("Is") }

func Unwrap() { _ = errors.Is(badUnwrap{}, context.Canceled) }
func Is()     { _ = errors.Is(badIs{}, context.DeadlineExceeded) }
```

`go test ./axiomcx/isctxerr/ -run . -count=1 -v`:

```
Unwrap panicked: string: Unwrap
Is panicked: string: Is
PASS
```

## Why the premises hold

- **`context.isTypedErr (interface.ok ⟨badUnwrap.ty, _⟩)`.** By definition this is
  `go.typeSetContains badUnwrap.ty go.error = true` (Perennial `Proof/context/Base.lean:182`). By
  `tsc_error` (`Proof/fmt/SprintfModel.lean:695`) that is
  `methodSet badUnwrap.ty !! "Error" = some (Signature [] false [string])`, which the program's
  generated `method_set` type assumption gives.
- **`isPkgInit errors` and `isPkgInit context`.** Both come from the program's `isPkgInit` (its
  dependencies).
- **`globalAddr context.Canceled ↦□ target`** (and likewise for `DeadlineExceeded`). Context's
  `isInit` gives both, through `#HCanceled` and `#HDeadlineExceeded`
  (`Proof/context/Base.lean:240-242`), and the Go code's load of `context.Canceled` reads that
  value.

## Lean proof sketch (phase 2)

`{{ isPkgInit isctxerr }} @! isctxerr.Unwrap #() {{ RET #(); True }}`:

1. Convert `badUnwrap{}` to `error`.
2. Load `context.Canceled` through its `↦□`.
3. `wp_apply errors.IsCtxErr.wp_proof`, with `isTypedErr` from `tsc_error` and the method set.
4. Take `RET b`, and the function returns.

`#print axioms` should show only this axiom and the generic ones.

## Reach and proposed restatement (applied, with corrections: see "Repaired")

The sweep-plan review recomputed the reach: 17 of 23 `_safe` roots, 137 roots in all. The users are:

- `EtcdServer.parseProposeCtxErr`, whose own spec also takes only `isTypedErr err`;
- `EtcdServer.LeaseRenew`;
- `v3rpc.watchServer.Watch`;
- `errors.IsDeadlineExceeded`'s spec text.

Proposed fix: replace the premise by Perennial's `isCtxErr err` (`Base.lean:212`), which is
exactly `Canceled`'s `*errorString` or `DeadlineExceeded`'s type. With it, both the `err == target`
comparison and the method lookups are determined. The callers pass `cctx.Err()`, and `isContext`'s
`HErr` gives `isCtxErr` for every non-nil `Err`. Carrying it through means changing
`parseProposeCtxErr`'s premise as well. The other option is `errorIsTree`, as
`IsDeadlineExceeded` does.

## Not tried

- **An error whose `Unwrap() []error` panics.** It takes the same path as `Unwrap`.
- **`err` with an incomparable dynamic type.** Go's `err == target` panics only when both have the
  same incomparable type, and the target's type is fixed and comparable, so this is not a path.
