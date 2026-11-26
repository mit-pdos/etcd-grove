# Axiom review: zerolog's 7 remaining event axioms (over the defined `eventTok`)

Reviewed 2026-11-26 by the `axiom` skill, read-only, in `/shared/etcd-grove-dsvr3` (branch `dsv-retire-3`
@ `b15cc31bb4`); zerolog v1.23.0 (`/root/go/pkg/mod/github.com/rs/zerolog@v1.23.0`: `event.go`,
`internal/json/{base,types,string}.go`); Go go1.27.3 (the pin of `etc/goose.py`). Tests:
`notes/axiom-review/dsv-zerolog-gotest/zl_test.go`.

## The axioms

`Dsverify/Proof/github_com/rs/zerolog/Event__{Int,Ints,Int64,Uint32,Bool,Float64,Msg}.lean`:

- `Event.F.wp_proof` (F a field method): `{{ isPkgInit zerolog ∗ eventTok e }} e.F(k, x) {{ RET #e; eventTok e }}`
  for every `e`, key `k`, value `x` (`w64`, `GoSlice`, `w64`, `w32`, `Bool`, `w64` bits).
- `Event.Msg.wp_proof`: `{{ isPkgInit zerolog ∗ eventTok e }} e.Msg(msg) {{ RET #(); True }}`.

`eventTok e` (`EventTok.lean`, now a public definition): `e = null`, or `e ↦ v ∗ v.buf' ↦* bs ∗
ownSliceCap v.buf' ∗ ⌜bs ≠ []⌝ ∗ ioutil.Discard ↦□ w ∗ ⌜v.w' = newLevelWriter w ∧ done = nil ∧ ch = nil ∧
stack = false ∧ level ∈ {-1,0,1,2,3}⌝`.

Claims in plain words: on such an event (or `nil`) the field methods return the receiver and keep the
token; `Msg` returns, the token is gone.

## Verdicts

| Axiom | Verdict |
|---|---|
| `Event.Int.wp_proof` | **sound** |
| `Event.Int64.wp_proof` | **sound** (unused by rabia: can be dropped) |
| `Event.Uint32.wp_proof` | **sound** |
| `Event.Bool.wp_proof` | **sound** |
| `Event.Float64.wp_proof` | **sound** (NaN/±Inf handled) |
| `Event.Msg.wp_proof` | **sound** |
| `Event.Ints.wp_proof` | **conditional**: no Go panic exists, but it reads the caller's slice with no permission (fix below; unused by rabia: drop it) |

No Go program of rabia's shape was found that panics and is provable from these axioms plus the proved
specs. Every post returns an `eventTok` the real state satisfies.

## Why each holds (Go code at v1.23.0)

**Field methods** (`event.go:385-391, 403-418, 475-481, 547-553, 601-607`): `if e == nil { return e }`
(the `nil` case of the token, returned as is), else `e.buf = enc.AppendX(enc.AppendKey(e.buf, key), x)`.
- `AppendKey` (`internal/json/base.go`) reads `dst[len(dst)-1]`: the only panic path on the buffer,
  excluded by `bs ≠ []` (and the post keeps it: a field method only appends).
- `AppendInt`/`AppendUint32`/`AppendBool` are `strconv.Append*` into `dst`: no panic path for any value
  (`MinInt64`, `MaxUint32` tested).
- `AppendFloat64` → `appendFloat` (`types.go:301-314`): NaN, `+Inf`, `-Inf` are appended as strings
  before `strconv.AppendFloat`; `-0`, `MaxFloat64`, the smallest denormal and a NaN with payload bits
  tested.
- `AppendInts` (`types.go:79-92`): `len(vals) == 0` (nil or empty) appends `[]`; else ranges the slice.
- Every append to `e.buf` reallocates as needed; the token owns the buffer and its capacity, and the
  post's `e ↦ v'` has the same `w`, `done`, `ch`, `stack`, `level` (the methods touch only `buf`).

**`Msg`** (`event.go:105-149`, `69-82`, `32-43`): `nil` returns at once. Else `msg`: hooks (`ch = nil`:
none), `AppendKey(buf, MessageFieldName)` (non-empty buffer), `done = nil` (no `defer`), `write`: level is
one of the five (`!= Disabled`), appends `}` `\n`, `e.w = newLevelWriter(Discard)` is
`levelWriterAdapter{io.discard{}}` (non-nil; `io.discard` is not a `LevelWriter`), whose `Write` returns
`len(p), nil`, so `ErrorHandler`/`fmt.Fprintf(os.Stderr)` are not reached; `putEvent` drops a buffer over
64 KiB or `Put`s the event. No panic, no exit. The level restriction excludes `Panic`/`Fatal` events (whose
`done` panics/exits; `done = nil` already excludes them).

## Attacks tried (all failed)

1. **`Msg` returns the event to the pool.** The token is consumed (post `True`), so the proof keeps nothing
   of the event the pool now holds; a later `Get` handing the same `*Event` out again (real Go does:
   `TestReuseAfterMsg`) is matched by the pool's `eventElem` going to the new holder. A client cannot
   keep a token across `Msg`: it is exclusive (`e ↦ v`, the buffer's `↦*` and `ownSliceCap` at fraction 1)
   and `Msg` takes it whole.
2. **Reuse after `Msg`** (`e.Msg(); e.Int(...)`, double `Msg`, i.e. double `putEvent`): in Go no panic
   but the pool then hands the same event to two `Info()` calls (`e1 == e2`: true in the test). Not
   provable: after `Msg` there is no token, and no axiom or proved spec gives one for nothing.
3. **A client-built token** (the definition is public). From another package Go can only write a whole
   `Event` value (`*p = *e`, `*p = zerolog.Event{}`); the zero value fails the token (`buf` empty,
   `w` nil ≠ `newLevelWriter w`). A copy `*p = *e` shares `e`'s buffer, and the buffer's ownership exists
   once: at most one of `p`, `e` holds a token at a time, and whichever does is a well-formed event the
   real methods handle (its own fields, its owned buffer). Writing `zerolog.Event`'s unexported fields
   is not Go. No token for a `w` other than `newLevelWriter` of `Discard`'s value: the token's
   `Discard ↦□ w` agrees with the package's, and that cell is persistent, so no program writes `Discard`.
4. **A disabled level's `nil` event**: every field method and `Msg` return at once on `nil`. Tested: all
   256 `int8` global levels × the five level methods × every field method (with the extreme values above)
   × `Msg("msg")`/`Msg("")`: 650 enabled, 630 `nil` events, no panic (`TestAllLevelsAllFields`).
5. **A buffer over 64 KiB**: a 70000-byte `Str`, a 20000-element `Ints`, then `Msg`, 100 times, then
   small events after: no panic (`TestBigBuffer`). `putEvent` silently drops the event; the token is gone
   either way, so the axiom claims nothing about it.
6. **Concurrency**: 16 goroutines on one `New(nil)` logger, each with its own events, cycling
   `SetGlobalLevel` through the five levels, under `-race`: no panic, no race report (`TestConcurrent`).
   One event in two goroutines needs two tokens: excluded (exclusive).
7. **zerolog's other package variables** (`MessageFieldName`, `ErrorHandler`, read by `Msg`): not in the
   package fact, and their points-tos are allocated by the (proved, generated) initializer `Init.lean` and
   dropped there, so no program can be proved to write them (a store has no permission); real values
   `"message"` and `nil`.
8. **Cross-world** (skill step 3): the axioms are WPs only; no entailment from persistent cells to a pure
   fact. Not applicable.

## The `Ints` condition, and the fix

`Event.Ints.wp_proof` takes `x : GoSlice` with **no permission on its elements**, yet `AppendInts` reads
them (`types.go:84-88`). A proof can therefore own `x ↦* xs` and write it from another goroutine while
`Ints` reads: a data race the model cannot see (Perennial's non-atomic loads are stuck against a store in
progress, so the axiom claims a model execution that is in fact stuck does not get stuck). It is **not** a
Go-panic counterexample: `[]int` elements are single machine words, so no torn value and no crash
(`TestIntsRacingWriter`, 20000 `Ints` calls against a writer loop, without `-race`: no panic; under `-race`
the detector reports the race only). Same shape as the dsv-fix4 review's "no permission on the logger" gap.

Fix (either):
- **Drop `Event_Ints` (and `Event_Int64`) from `EventSpecs`** and retire the two axioms: rabia calls
  neither (its only `Ints` calls are commented out, `roles/server/layers/consensus/executor.go:523,541`;
  no `Int64` call); `HypsHoldLinked.lean:46` is their only use, and no rabia proof reads
  `hE.Event_Ints`/`hE.Event_Int64`. Two fewer axioms in the trust base.
- Or restate `Ints` with the slice's read permission returned:
  `{{ isPkgInit ∗ eventTok e ∗ x ↦*{dq} xs }} e.Ints(k, x) {{ RET #e; eventTok e ∗ x ↦*{dq} xs }}`.

## Remarks (no action needed for soundness)

- The token is stronger than `Msg` needs (it could allow `Disabled`, `NoLevel`, any `done = nil` event):
  harmless, and exactly what the proved level methods produce.
- `ioutil`'s package fact is `∃ w, Discard ↦□ w` with `w` unconstrained; `Msg`'s truth rests on the real
  `w` being `io.discard{}`, which it is in every execution (only `ioutil`'s initializer writes it, and the
  cell is persistent afterwards). Pinning `w` in `ioutil`'s fact would make that explicit; it is what
  `Msg`'s eventual proof (once Perennial has `io.Discard`'s `Write` spec) needs.

## Not tried

A Lean proof of anything (no counterexample found; read-only brief). The `-race` run of the racing `Ints`
writer was stopped (slow under the detector); the plain run is the panic check.
