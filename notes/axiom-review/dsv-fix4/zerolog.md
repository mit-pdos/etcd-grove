# Axiom review: `github.com/rs/zerolog` (16 axioms over `eventTok`)

Reviewed 2026-11-25 by the `axiom` skill (an independent reviewer), in the worktree
`/shared/etcd-grove-mathrand` (branch `dsv-fix4`) at `a28755b089`; Perennial `fce59af75`; zerolog
v1.23.0 (`~/go/pkg/mod/github.com/rs/zerolog@v1.23.0`: `log.go`, `event.go`, `globals.go`); Go
go1.27.1 for the tests (the pinned go1.27.3 was not fetchable offline; nothing here depends on the
patch release: zerolog's paths are plain Go).

## The axioms

All in `Dsverify/Proof/github_com/rs/zerolog/`, the triples in `Spec.lean`, the token `eventTok`
(`EventTok.lean`, an `opaque` with no laws), the package fact `True` (`Base.lean`):

- `Logger.{Trace,Debug,Info,Warn,Error}.wp_proof` (`Logger.level.spec eventTok m`): for every
  `l : Loc`, `l ≠ null`, `{{ isPkgInit }} l.M() {{ e, RET #e; eventTok e }}`. **No resource of `l`
  is asked**: no points-to, no fact about the `Logger` value stored there.
- `Event.{Str,Int,Ints,Int64,Uint32,Bool,Float64}.wp_proof`: `{{ isPkgInit ∗ eventTok e }} e.F(k, x)
  {{ RET #e; eventTok e }}`, every `k`, every `x`.
- `Event.Msg.wp_proof`: `{{ isPkgInit ∗ eventTok e }} e.Msg(msg) {{ RET #(); True }}`.
- `ParseLevel.wp_proofWarn`: `ParseLevel("warn")` returns `(2, nil)`.
- `SetGlobalLevel.wp_proof`: every `lv : w8`, returns.
- `New.wp_proof`: **every** `w : GoInterface`, `New(w)` returns some `lg : Logger`, post `True`.
- `wp_initialize'` (`Init.lean`): reviewed separately, `notes/axiom-review/dsv-inits/github-com-rs-zerolog.md`.

Claims in plain words: a logger's level method never panics on a non-nil pointer, whatever logger
it points to and whatever else happens to that memory; field methods never panic; **`Msg` never
panics, whatever logger made the event**; `New` accepts any writer.

(At `a28755b089` rabia's proofs still take the class `Hyps` (`Spec.lean`), whose fields are the same
triples with an existential token; the axioms are in `etc/tcb-baseline.txt` and
`etc/tcb-collections/dsv-rabia.txt`. The finding below holds for both forms: `Hyps.New` is the same
statement.)

## Verdict: **refuted** (`New.wp_proof` with `Event.Msg.wp_proof`); the rest survives, with conditions

### The counterexample

`New` takes any writer, and `Msg` writes to it (`event.go:132-149` `msg` → `write`, `event.go:77-78`
`e.w.WriteLevel(e.level, e.buf)`; `levelWriterAdapter.WriteLevel` calls `w.Write`), with no `recover`.
`New` (`log.go:205-214`) replaces only a `nil` interface by `ioutil.Discard`. So:

```go
type panicWriter struct{}
func (panicWriter) Write(p []byte) (int, error) { panic("writer panics") }

func Main() {
	l := zerolog.New(panicWriter{})
	l.Info().Str("k", "v").Msg("x")
}

// without a panic in user code: a typed-nil writer
func Main2() {
	var b *bytes.Buffer
	l := zerolog.New(b) // a non-nil interface: not replaced by Discard
	l.Warn().Msg("x")   // (*bytes.Buffer)(nil).Write: nil dereference
}
```

Test output (scratch module, zerolog v1.23.0, default global level `Debug`, so `Info`/`Warn` are
enabled; `go test -race -v`):

```
=== RUN   TestWriterPanics
    zlcx_test.go:31: Main: recovered writer panics
=== RUN   TestNilBufferWriter
    zlcx_test.go:31: Main2: recovered runtime error: invalid memory address or nil pointer dereference
```

The triple `{{ isPkgInit zerolog }} Main #() {{ RET #(); True }}` follows from the axioms alone:
`wp_apply New.wp_proof` (any `w`), allocate the local `l` (a typed points-to, so `l ≠ null` by
`typedPointsto_not_null`), `wp_apply Logger.Info.wp_proof`, `Event.Str.wp_proof`,
`Event.Msg.wp_proof`. `panicWriter.Write` is never reached in the model: the axiom for `Msg` covers
the call. This is the chain `Server.TerminalLogger.wp_proof`
(`Dsverify/Proof/rabia/roles/server/Server__TerminalLogger.lean`) already runs, with `w` generalized
from `nil`. The Lean proof was **not built** (the brief was read-only on the repository: no Goose
project could be added for the program); Main2 needs a Goose translation of `bytes.Buffer` as a
writer, Main only a user type with a `Write` method.

### A second gap (not tested): no permission on the logger

`Logger.level.spec` asks nothing of `l`, yet `newEvent`/`should` (`log.go:420-449`) read `l.level`,
`l.w`, `l.sampler`, `l.hooks`, `l.context`, `l.stack`. A proof may therefore own `l ↦ lg` and
overwrite it (`*lp = zerolog.New(otherWriter)`) in one goroutine while another calls `lp.Info()`:
a race the model does not see, and in Go a torn two-word interface read of `l.w` (an itab of one
writer type with the data word of another) can crash at `WriteLevel`. Not driven to a crash here
(a timing-dependent fault); it disappears with the same fix.

### Rabia

Rabia is not affected in substance: `InitLogger` (`internal/logger/logger.go:87-96`) calls only
`zerolog.New(nil)` (the writer becomes `ioutil.Discard`, whose `Write` never panics), loggers are
stored in struct fields and written once at construction. The false statement is in the trust base
of `dsv-rabia`, not in rabia's Go code. **No bug in the verified Go code.**

### Proposed restatement (not applied)

- `New.spec`: restrict the writer to what rabia passes, `w = interface.nil` (or, more generally, a
  writer whose `Write` has a no-panic spec, given as a premise), and return an opaque persistent
  `loggerOk lg`.
- `Logger.level.spec`: take `l ↦□ lg ∗ loggerOk lg` (or a fraction `l ↦{#q} lg`, returned), so a
  logger made by another path (`Output`, `Hook`, a sampler) or one being overwritten has no spec.

## Attacks that failed (the conditions the rest survives on)

1. **Event reuse after `Msg` (the pool).** `Msg` consumes the token and `eventTok` is opaque with no
   law (no duplication, no persistence, no `True ⊢ eventTok e`): a proof cannot call a method on
   an event after `Msg`, nor hold two tokens for one live event (the pool hands a pooled `*Event`
   out again only after `putEvent`, i.e. after its token was consumed).
2. **A `nil` event / disabled level.** Every method on a `nil` `*Event` returns at once
   (`event.go:71`, `105`, and each field method's `if e == nil`); `should` returns false for any
   level below `l.level` or `GlobalLevel()`. Tested with `SetGlobalLevel` of -100, -1..7, 100 and all
   five level methods: no panic. `Panic()`/`Fatal()` are not axiomatized.
3. **Concurrency on one event.** The token is exclusive (no law makes it shareable): two goroutines
   cannot both hold it. **On one logger**: with `New(nil)` (Discard) concurrent `Info().Int().Msg()`
   from 8 goroutines under `-race`: no report, no panic. Other writers: see the refutation.
4. **Hooks, sampler, `context`, `stack`, `done`.** Reachable only through unaxiomatized API
   (`Hook`, `Sample`, `With`, `Panic`/`Fatal`), where a proof gets stuck; a zero `Logger{}` has none
   and `w == nil`, which `write` skips (`event.go:77`): tested, no panic.
5. **`LevelFieldMarshalFunc`, `ErrorHandler`, `MessageFieldName` changed** (used by `newEvent`,
   `msg`, and by `ParseLevel`, `log.go:160-182`, whose `"warn"` result depends on it). Condition:
   nothing writes zerolog's package variables. Holds in the model: the package fact is `True`, so no
   proof holds a points-to to any zerolog global and a store to one is stuck.
6. **Field arguments.** `Ints` with a `nil` or huge slice, `Str` with invalid UTF-8, `Float64` of
   NaN/Inf bits, `Uint32`/`Int64` extremes: the JSON encoder appends; no panic path (a huge buffer
   costs memory only; `putEvent` drops buffers over 64 KiB). `Float64`'s `x : w64` is the bits.
7. **`SetGlobalLevel(lv)` any `lv`**: an atomic store (`globals.go:114-116`). **`ParseLevel("warn")`**
   is `(WarnLevel = 2, nil)` under condition 5; tested.
8. **`New(nil)`, a `Logger` copied vs a pointer**: `New(nil)` uses Discard; the methods have pointer
   receivers and read the copy at `l`; tested.
9. **Token from nothing / cross-world.** `eventTok` is an `opaque` whose body (`True`) the kernel
   does not unfold, and it has no law; no entailment from persistent cells concludes a pure fact
   (`crossWorld` check: not applicable).

Not tried: a Lean proof of the counterexample (read-only brief), a driven crash for the logger race
(section above), broken-pipe `SIGPIPE` on a stdout writer (a kill, not a panic; rabia writes nowhere).
