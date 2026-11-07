# zap's logger on a zero `Logger` (axiom review, 2026-11-07)

**Reviewed** (lean at `ad87892323`, sweep target B1-2): the trust-boundary axioms
`zap.Logger.{Debug,Info,Warn,Error,Panic,Fatal,Check}.wp_proof` (`Proof/go_uber_org/zap/Logger__*.lean`,
triples in `Spec/go_uber_org/zap/Logger__*.lean`) and `zapcore.CheckedEntry.Write.wp_proof`
(`Spec/go_uber_org/zap/zapcore/CheckedEntry__Write.lean`). The Go code is zap v1.28.0, the version
`examples/go.mod` pins, run with `GOTOOLCHAIN=go1.27.3`.

## Verdict

**Refuted (Go side). The Lean side has not been built yet.** Each logger spec's only premise is
`isPkgInit zap ∗ ⌜l ≠ null⌝`, and `CheckedEntry.Write`'s is `⌜ce ≠ null⌝`. No `zapLoggerOk`-style
predicate exists, so a program meets the premise with the zero struct (`&zap.Logger{}` or
`new(zap.Logger)`) and the fresh location the allocation returns. In Go:

- `Debug`, `Info`, `Warn` and `Error` panic. So does `Check` at any level below `DPanicLevel`.
  `Logger.check` calls `log.core.Enabled(lvl)` on the nil `core` (`logger.go:331`).
- `Fatal` and `Panic` panic too. From `DPanicLevel` up, `check` skips `Enabled` and calls
  `log.clock.Now()` on the nil `clock` (`logger.go:339`).
  - `Fatal`'s spec has post `False` (the process exits), so this panic refutes it.
  - `Panic`'s post is `r = PanicV #msg`. Go also panics, with a runtime error instead of the
    message, and only a `recover` can tell the two apart. So `Panic` is **not** refuted by a triple.
- `CheckedEntry.Write` panics when called twice on `&zapcore.CheckedEntry{ErrorOutput: w}`.
  - The first call marks the entry `dirty`.
  - The second reports the re-use to `ce.ErrorOutput` through `fmt.Fprintf`
    (`zapcore/entry.go:251-263`). `fmt` does not recover a panic in the writer's `Write`, so a
    `WriteSyncer` whose `Write` panics crashes the program.

`audit.md:297-299` argued "ok" from what etcd does ("etcd never sets … a fatal hook"). The specs'
premise does not say that.

## The program and its run

`examples/axiomcx/zap-zero/zapzero.go` (package `zapzero`), with one function per spec, for example:

```go
func Warn() { l := &zap.Logger{}; l.Warn("x") }
func Check() { l := new(zap.Logger); _ = l.Check(zapcore.WarnLevel, "x") }
func Fatal() { l := &zap.Logger{}; l.Fatal("x") }

type badWS struct{}
func (badWS) Write(p []byte) (int, error) { panic("badWS.Write") }
func (badWS) Sync() error                  { return nil }

func CheckedEntryWrite() {
	ce := &zapcore.CheckedEntry{ErrorOutput: badWS{}}
	ce.Write()
	ce.Write()
}
```

`go test ./axiomcx/zap-zero/ -run . -count=1 -v`. Each test checks that its function panics:

```
Warn panicked: runtime.errorString: runtime error: invalid memory address or nil pointer dereference
Info / Debug / Error / Check / Fatal / Panic: the same
CheckedEntryWrite panicked: string: badWS.Write
PASS
```

## Why the premises hold

- **`isPkgInit zap` and `isPkgInit zapcore`.** `zapzero` imports both, so the program's own
  `isPkgInit` gives them, as for every example. Each package's `Init.lean` is generated.
- **`l ≠ null`.** The allocation of the zero `Logger` returns a fresh, non-null location.
- **The types are not sorry'd.**
  - `zap.Logger` is translated with its fields (`Code/go_uber_org/zap.lean:1383`), and its generated
    instances are proved (`GeneratedProof/go_uber_org/zap.lean:432` on).
  - So are those of its field types (`zapcore.Core`, `CheckWriteHook`, `WriteSyncer`,
    `LevelEnabler`, `Clock`) and of `zapcore.CheckedEntry` and `Entry`.
  - The `sorry -- axiomatized type` instances in zap are `durations`, `times`, `AtomicLevel`,
    `Sink` and `sinkRegistry`; in zapcore, `BufferedWriteSyncer`, `Encoder`, `jsonEncoder`,
    `lazyWithCore`, `counter` and `lockedWriteSyncer`. The program reaches none of them.
- **Variadic calls.** Goose passes a nil `fields` slice for a call with no fields, and the specs
  quantify over every `fields`.

## Lean proof sketch (phase 2)

`{{ isPkgInit zapzero }} @! zapzero.Warn #() {{ RET #(); True }}`:

1. `wp_alloc` the zero `Logger`.
2. `wp_apply zap.Logger.Warn.wp_proof` with `l ≠ null` from the allocation.
3. Finish with `RET #()`.

The other functions follow the same shape:

- `Info`, `Debug`, `Error` and `Check` are the same.
- `Fatal`'s post `False` closes the goal.
- `CheckedEntryWrite`:
  1. Allocate the struct literal, with `badWS{}` converted to the `WriteSyncer` interface.
  2. Apply the `Write` axiom twice.

  The methods of `badWS` are translated but never called in the proof. `#print axioms` should show
  only the axiom under review and the generic ones.

## Reach and proposed restatement (not applied)

The plan's reach counts are `Panic` 84/17, `Error` 82/17, `Warn` 76/17, `Debug` 65/17, `Info` 63/17
and `Fatal` 49/17. `Check` and `CheckedEntry.Write` are used only by
`auth.authStore.Authenticate`. The proposed restatement:

- **A persistent `zapLogger l`** that only the constructors give: `zap.NewNop`'s spec, and whatever
  produces the logger etcd's configuration holds. Every logger method requires it in place of
  `⌜l ≠ null⌝`. The callers' premises (the server's `cfg.Logger`, the backend's and the lessor's
  `lg`) then carry `zapLogger lg` up to the adequacy theorems' startup premises.
- **An exclusive `zapEntry ce`** that `Check` returns when it returns non-nil, and that `Write`
  consumes. That rules out a double `Write` as well as an entry built by hand.

## Not tried

- **A logger built with `zap.WithFatalHook(zapcore.WriteThenPanic)`.** Its `Fatal` panics. It needs
  a spec for `zap.New`, and none exists.
- **`recover`-based observation of `Panic`'s value.**
