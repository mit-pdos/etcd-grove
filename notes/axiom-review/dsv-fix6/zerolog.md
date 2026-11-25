# Axiom review: zerolog v1.23.0's per-function axioms (dsv-fix6)

Reviewed 2026-11-25 by the `axiom` skill (an independent reviewer), in the worktree
`/shared/etcd-grove-dsvfix6` (branch `dsv-fix6`, `d7c5b56a4e` plus the uncommitted working-tree edits,
the version reviewed); Perennial `fce59af75`; zerolog v1.23.0 from the module cache
(`/root/go/pkg/mod/github.com/rs/zerolog@v1.23.0`); Go at the pinned toolchain go1.27.3. Read-only
review: the brief allowed no branch, translation or Lean file in the repository, so the attacks are
Go tests (run, scratch module, deleted after) and arguments about what a Lean proof could derive, not
machine-checked proofs. The dsv-fix4 review of the same library was not read (independence).

## The axioms

All in `Dsverify/Proof/github_com/rs/zerolog/`, over the predicates of `Spec.lean` and `EventTok.lean`;
the package fact (`Base.lean`) is `isPkgInit zerolog = True`.

- `New.wp_proof` (`New.lean`): `{{ isPkgInit }} New(nil) {{ (lg : Logger), RET #lg; loggerOk lg }}`,
  `loggerOk lg = □ loggerMade lg`, `loggerMade` opaque, no law: only this axiom produces it.
- `Logger.{Trace,Debug,Info,Warn,Error}.wp_proof` (`Logger__*.lean`, `Logger.level.spec`):
  `{{ isPkgInit ∗ l ↦{dq} lg ∗ loggerOk lg }} l.M() {{ (e : Loc), RET #e; l ↦{dq} lg ∗ eventTok e }}`.
- `Event.{Str,Int,Ints,Int64,Uint32,Bool,Float64}.wp_proof` (`Event__*.lean`):
  `{{ isPkgInit ∗ eventTok e }} e.M(k, x) {{ RET #e; eventTok e }}`, for every key and value (`Ints`:
  any `GoSlice`, no points-to of its elements asked).
- `Event.Msg.wp_proof` (`Event__Msg.lean`): `{{ isPkgInit ∗ eventTok e }} e.Msg(msg) {{ RET #(); True }}`.
- `ParseLevel.wp_proofWarn` (`ParseLevel.lean`): `ParseLevel("warn")` returns `(W8 2, nil)`.
- `SetGlobalLevel.wp_proof` (`SetGlobalLevel.lean`): `SetGlobalLevel(lv)` returns, every `lv : w8`.

`eventTok : Loc → IProp` is opaque, not persistent, with no law (no duplication, no pure fact).
`HypsHoldLinked.lean` assembles them into `Hyps` (no other content). Out of scope: `Init.lean`'s
`wp_initialize'`.

Claims, in plain words: `New(nil)` returns; the five level methods on a logger made by `New(nil)`
neither panic nor change the logger, and return an event (or `nil`) the caller alone holds; the field
methods return their receiver; `Msg` returns, at any global level; `ParseLevel("warn")` is `(2, nil)`;
`SetGlobalLevel` never panics.

## Verdict: **survives**

No program that panics when run and has a no-panic triple from these axioms was found. Conditions it
rests on (each checked below):

1. **No provable program can write zerolog's or `io/ioutil`'s package variables.** Every real panic
   found through the covered API needs such a write (`LevelFieldMarshalFunc`, `LevelWarnValue`,
   `ioutil.Discard`, ...). The globals' points-tos are made only by `go.GlobalAlloc` inside a
   package's own `initialize'` (`Perennial/Golang/Theory/PostLifting.lean`, `wp_GlobalAlloc`), which
   for zerolog and `io/ioutil` (names only, `Dsverify/Proof/io/ioutil/Base.lean`: `isPkgInit = True`)
   is an axiom whose post gives only `isPkgInit = True`: the points-tos are never handed out, so a
   store to `zerolog.X` or `ioutil.Discard` has no WP. If a future spec, model or package fact hands
   out a writable points-to of any of these variables (`LevelFieldMarshalFunc`, `LevelFieldName`,
   `Level*Value`, `MessageFieldName`, `ErrorHandler`, `ioutil.Discard`), the axioms become false and
   must be re-reviewed (a full points-to: the `↦□ DFrac.discard` style of Perennial's `io.isInit`
   would be harmless).
2. **`loggerOk` stays tied to `New(nil)`**: `loggerMade` is opaque with no law in the repository
   (grep: no other mention outside the zerolog directory), and a `Logger` made by `New(nil)` is a pure
   value (`w = levelWriterAdapter{discard{}}`, `level = TraceLevel`, nil `context`/`hooks`/`sampler`):
   every Go value equal to it as a Lean value behaves identically, so copies are sound.

## Attacks that failed

Scratch module `axrev/zl` (zerolog v1.23.0, offline, `GOTOOLCHAIN=go1.27.3 go test -count=1 -v`):

```
=== RUN   TestGlobals
LevelFieldMarshalFunc=nil; Info() panics: true
ioutil.Discard=panicW; New(nil).Info().Msg panics: true
LevelWarnValue changed; ParseLevel(warn) err panics: true
Output(panicW) logger, Info().Msg panics: true
Str after Msg on reused event panics: false
--- PASS: TestGlobals (0.00s)
warn 2 false
debug 0 false
trace -1 false
 6 false
foo 6 true
Warn 6 true
--- PASS: TestParse (0.00s)
--- PASS: TestAllLevels (6.78s)
--- PASS: TestConcurrent (9.97s)
--- PASS: TestIntsRace (0.02s)
PASS
```

1. *Missing premise, field and level methods at the boundaries* (`TestAllLevels`): for every global
   level `-128..127` (`SetGlobalLevel` over all of `w8`), on a `New(nil)` logger and a copy of it,
   each of the five level methods, then every covered field method with extreme values (`MinInt64`,
   `MaxUint32`, NaN, ±Inf, the smallest subnormal, invalid UTF-8, an empty key, a 128 KiB key, a nil
   and a non-empty `Ints` slice), then `Msg` with an empty, a non-empty and an invalid-UTF-8 message.
   No panic: field methods only append to the buffer (`event.go:232-607`, NaN/Inf written as strings,
   `internal/json/types.go:301`); the level methods' `newEvent` (`log.go`) reads the logger and calls
   `LevelFieldMarshalFunc`, which is `Level.String`; `Msg` (`event.go:113`, `msg`, `write`) writes to
   `ioutil.Discard` (never fails, so `ErrorHandler` is not reached) and `putEvent`s.
2. *Package variables* (`TestGlobals`): `LevelFieldMarshalFunc = nil` makes `Info()` panic (nil func
   call, `log.go` `newEvent`); `ioutil.Discard = panicW{}` before `New(nil)` makes `Msg` panic in the
   writer (`New` reads `ioutil.Discard`, `log.go` `New`); changing `LevelWarnValue` makes
   `ParseLevel("warn")` return an error (`log.go` `ParseLevel` compares against
   `LevelFieldMarshalFunc(level)`). Real panics, but not provable: condition 1 (no points-to of the
   variables, so the program's store has no WP).
3. *A logger not made by `New(nil)`* (`Output(panicW)`, `Hook`, `With().Logger()`, a zero `Logger{}`):
   `Output(panicW{})` panics in `Msg`, but the result has no `loggerOk` (no spec of `Output`/`Hook`/
   `With`; `loggerMade` has no law); overwriting a logger's cell with such a value needs the full
   points-to, after which the level axioms ask `loggerOk` of the new value. (A zero `Logger{}` does
   not even panic: `e.w = nil`, `write` skips it.)
4. *Too much ownership of events* (pool reuse): `Msg` returns the event to `eventPool`
   (`event.go` `write`/`putEvent`), and the next level method may return the same pointer with a
   fresh `eventTok`. The old holder's token was consumed by `Msg`, so no proof can call a method of
   the old pointer afterwards; the reuse in Go (`Str` after `Msg`) does not panic anyway
   ("Str after Msg ... panics: false"). Two `nil` events get two tokens; harmless (every method returns
   at once on `nil`). No law duplicates `eventTok` or derives a pure fact from it.
5. *Concurrency* (`TestConcurrent`): 64 goroutines share one `New(nil)` logger (the fractional
   points-to of the spec: zerolog only reads it), race `SetGlobalLevel` (atomic, `globals.go`), and
   pass each event through a channel before its field methods and `Msg` (the token moving between
   threads). 128000 events, no panic. `sync.Pool` gives the happens-before between a `putEvent` and
   the next `Get`.
6. *`Ints` without ownership of the slice* (`TestIntsRace`): the axiom asks no points-to of `x`, so a
   proof can call it while another thread writes the elements. In Go this is a data race on `int`s that
   reads torn-free words and never panics (no counterexample by the skill's rules; a race the detector
   would report is not one). A modelling looseness, not a soundness gap for panics; the spec would read
   better with `x ↦*{dq} xs` given back.
7. *`ParseLevel("warn")`*: `(WarnLevel = 2, nil)` at the default globals (`TestParse`); `Level` is
   `int8`, so `W8 2` is its representation.
8. *Cross-world* (the skill's check): no entailment or law has bare persistent cells on the left and a
   pure equation on the right; `loggerOk`/`eventTok` are opaque predicates with no laws. Not applicable.
9. *Exit*: the five levels pass `done = nil` (`log.go:294-324`), so `Msg` never reaches
   `os.Exit`/`panic` (those are `Fatal`/`Panic`, which have no axiom).

Not tried: a machine-checked Lean proof of any attack (none got a Go panic past condition 1, so none
was a candidate); `-race` runs of the tests (started, slow; the race detector's reports are not
panics in any case).

## Findings in the Go code

- zerolog v1.23.0: none (its documented "Calling Msg twice can have unexpected result" is excluded by
  the token being consumed).
- rabia (`examples/dsverify/rabia/internal/logger/logger.go:63-73`, `GetLogLevel`): the comment says
  "If options other than "debug", "info", and "warn" are given, this function selects the debug level",
  but the code panics on any string `ParseLevel` rejects (`"foo"`, `"Warn"`: the test's `true` error
  column), and accepts `""` (an unset `RC_LLevel`, `config.go:128`) as `NoLevel` (6), which disables
  every level, and `"trace"`, `"error"`, ... as themselves. A documentation/code mismatch (the kit sets
  `"warn"`, `kit.go:216`, so it does not block the proof); not recorded in `nonissues/` by this
  read-only review.
