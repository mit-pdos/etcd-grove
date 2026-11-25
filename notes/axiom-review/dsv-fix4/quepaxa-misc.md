# Axiom review: QuePaxa's `time.Time.UTC`, `sort.Ints`, `fmt.Println` (dsv-fix4)

Reviewed 2026-11-25 by the `axiom` skill (an independent reviewer), in the worktree
`/shared/etcd-grove-mathrand` (branch `dsv-fix4`, at `5c6274f9e0` plus the uncommitted files);
Perennial `fce59af75`; Go at the pinned toolchain go1.27.3 (`src/time/time.go`, `src/sort/sort.go`,
`src/slices/sort.go`, `src/fmt/print.go`, `src/os/file.go`). Read-only review: no Lean
counterexample was attempted, since no gap was found to build one on.

**Retired 2026-11-25** (#49 step 1, branch `dsv-retire-1`): `time.Time.UTC` and `sort.Ints`. Perennial
(branch `retire1-sort-time`, `596a47b9f`) translates `Time.UTC`, `Time.setLoc` and `sort.Ints` and proves
them (`time.Time.wp_UTC`, `sort.wp_Ints`); `Dsverify/Proof/{time/Time__UTC,sort/Ints}.lean` are now
theorems from those. `fmt.Println` stays.

## The axioms

Each is the field of a former premise class of QuePaxa's statement (`UtcHyp`, `SortHyp`,
`PrintlnHyp`), verbatim; the specs are in `Dsverify/Proof/raxos/Hyp.lean`.

- `raxos.hyp.time.Time.UTC.wp_proof` (`Dsverify/Proof/time/Time__UTC.lean`):
  `∀ t, {{ True }} t.UTC() {{ (t' : time.Time), RET #t'; True }}`.
- `raxos.hyp.sort.Ints.wp_proof` (`Dsverify/Proof/sort/Ints.lean`): for `data ↦* xs`
  (`xs : List w64`, `len ≤ 2^62`) and `isPkgInit sort`, `sort.Ints(data)` returns with
  `data ↦* xs'`, `xs ≡ₚ xs'`, and `xs'` ascending by `sint.Z`.
- `raxos.hyp.fmt.Println.wp_proof` (`Dsverify/Proof/fmt/Println.lean`): for `isPkgInit fmt`,
  `□ [∗list] x ∈ xs, printOk x` and `arg ↦*{dq} xs`, `fmt.Println(arg...)` returns some `(n, err)`
  and gives back `arg ↦*{dq} xs`. `printOk x` is `nil`/`fmt.ArgWf` (Perennial's: a predeclared
  basic type, or a named integer/string type with `NoFmtMethods`: no `Format`, `GoString`, `Error`,
  `String` of any signature), or `models_lab.errAny x` (a non-nil error whose `Error()` has a
  resource-free, persistent WP returning some string) together with "the dynamic type is not in
  `fmt.Formatter`'s type set".

Perennial translates none of the three (names only), so each call resolves through the context's
opaque function table.

Callers: `examples/dsverify/quepaxa/replica/src/proxy.go:221` (`rand.Seed(time.Now().UTC().UnixNano())`),
`proxymabhandler.go:334` (`sort.Ints(epochTimes1)`, a fresh local `[]int`), `proxynetwork.go:55,60`
(`fmt.Println("...", err)` after a failed `Accept`/`io.ReadFull`), proved in
`Dsverify/Proof/raxos/Proxy/NetPrint.lean` (`printOk_str_err`) and `NetAccept.lean:165,264`;
instantiated in `Dsverify/Proof/raxos/examples/quepaxanet/TopLevelRobustness.lean:162-164`.

## Verdicts

- `time.Time.UTC.wp_proof`: **survives**.
- `sort.Ints.wp_proof`: **survives**.
- `fmt.Println.wp_proof`: **survives with a condition**: it says nothing about `os.Stdout`, which
  Go's `Println` writes through; it is sound today only because Perennial's model leaves the
  variable `os.Stdout` unallocated (no program that writes or reads it has a proof). See attack P7.

Plus, for all three, the generic context condition of every names-only trust-boundary axiom
(`sort-slice.md`, attack 9): stated for every `GoGlobalContext`/`go.Semantics`, true only in the
contexts where the names resolve to Go's code.

## Attacks tried

### `(time.Time).UTC`

U1. **Panics.** `UTC` (`time.go:1368`) is `t.setLoc(&utcLoc); return t` on the receiver's copy;
`setLoc` (`:217`) compares the pointer, calls `stripMono` (`:226`: integer arithmetic through
`sec`, `:181`, wrapping, no division) and stores `t.loc` in the copy. No dereference of `t.loc`, no
panic for any field values, so arbitrary Lean `Time` records (zero, any `loc` pointer, any
`wall`/`ext`) are fine. Tested: the zero `Time`, `time.Now()` (monotonic), `Unix(MaxInt64,
999999999)`, `Unix(MinInt64, 0)`, a `FixedZone` time: no panic.
U2. **Precondition `True` (no `isPkgInit time`).** `UTC` takes `&utcLoc`'s address only, never reads
it; nothing depends on `time`'s initialization.
U3. **Effects / frame.** Value receiver, no global writes; the post claims nothing about `t'`, so
no false pure fact is available.

### `sort.Ints`

S1. **Body.** `func Ints(x []int) { slices.Sort(x) }` (`sort.go:170`); `slices.Sort` is
`pdqsortOrdered` with `cmpLess` (`x < y`, the NaN test `x != x` is false for integers): signed
64-bit order, matching `sint.Z` on `w64` (Goose's `int`). Only swaps within `[0, len)`: a
permutation, ascending; for a total order on values the sorted permutation is unique.
S2. **Nil, empty, one element.** No-ops; tested.
S3. **Extremes and duplicates.** 20,000 random slices (length 0-299, `MinInt`, `MaxInt`, many
duplicates and negatives) sorted through a sub-slice of a larger array: all equal a reference sort
by signed comparison, the backing array beyond `len` unchanged (the frame: the post's `data ↦*`
covers only `len` cells, `cap` is untouched).
S4. **Concurrency.** The pre owns `data ↦* xs` fully; Go's sort starts no goroutine.
S5. **Type confusion.** `xs : List w64` does not fix `int` vs `uint64`, but a Go program can pass
only a `[]int` (or a named type with underlying `[]int`) to `sort.Ints`; a translated program never
hands it a `[]uint64`, whose unsigned order would differ.
S6. **The length bound** only restricts the callers; Go has no limit below `MaxInt`.

### `fmt.Println`

`Println` is `Fprintln(os.Stdout, a...)` (`print.go:306`); each operand goes through `printArg(arg,
'v')` (`:674`): `nil` prints `<nil>`; predeclared basic types are formatted by the type switch with
no method call; anything else goes to `handleMethods` (`:614`) then `printValue`.

P1. **`Format` (the sibling `log.Logger.Printf` finding).** `handleMethods` calls `Format` of any
`Formatter` under every verb (`:630`). `printOk` excludes it on both sides: `ArgWf`'s named types
need `NoFmtMethods` (no `Format` of any signature), and the `errAny` disjunct requires
`typeSetContains ty fmt.Formatter.ty = false`. That fact is signature-exact
(`typeSetElemContains_method`), as Go's type assertion is, and Goose's `MethodSetIs` facts come from
`types.NewMethodSet` (promoted methods included, `goose/lean_types.go:291`), so an embedded
`Formatter` is excluded too. The excluded case is exactly the one Go calls.
P2. **`GoString`.** Called only under `%#v` (`sharpV`); `Println` uses `%v`. Tested: an error type
with `GoString` and `String` that write caller memory, printed by `Println`: neither is called.
P3. **`String` of an error.** Under `%v`, `case error:` (`:657`) precedes `case Stringer:` (`:663`):
only `Error()` is called (same test).
P4. **`Error()` behaviour.** `errAny` gives a persistent, resource-free WP of `Error()` returning a
string, so `Error()` can neither panic in the model nor touch memory the caller owns (it holds no
resource; at most it opens invariants, which the caller then does not own exclusively). In Go a
panicking `Error()` is recovered by `catchPanic` (`:580`; tested: `%!v(PANIC=Error method: boom)`),
and a nil pointer receiver prints `<nil>` (tested). The one unrecovered case, a nested panic
(`Error()` panics with a value whose `String` panics: `:591`, re-panic; tested: panics), needs an
`Error()` that panics, which `errAny` excludes.
P5. **Named basic types / `printValue`.** Reached only for `ArgWf` named integer/string types with
`NoFmtMethods`: `handleMethods` finds nothing, `printValue` formats the integer or string kind,
reading no memory. Tested with `type NI int64`.
P6. **Reads of memory the axiom does not ask for.** Operands are immediate values (basic) or
errors whose reads are inside `Error()`'s WP; the slice is read under `arg ↦*{dq}`. No
unsynchronized read (unlike the `log` review's attack 9, `printOk` admits no pointer to a struct).
P7. **`os.Stdout`.** Go's `Println` writes through `os.Stdout`, a package variable a program may
assign. Tested: `os.Stdout = &os.File{}` (legal outside `os`: an empty composite literal) then
`fmt.Println("x")` panics (`runtime error: invalid memory address or nil pointer dereference`,
`(*File).Write` → `f.write` on the nil `*file`). The axiom asks nothing about `os.Stdout`. No
counterexample today: Perennial's trusted `os.Stdout.init` (`Perennial/TrustedCode/os.lean:73-80`)
does not allocate the variable, so a store to (or load of) `os.Stdout` is stuck and such a program
has no proof. **Condition:** when Perennial gives `os.Stdout` a real model (perennial#663, a
writable variable), this axiom becomes false as stated; it then needs a premise that `os.Stdout`
holds a valid `*File` (e.g. `os`'s invariant over the variable), or its discharge through
Perennial's `Fprintln`. `os.Stdout = nil` does not panic (`checkValid` returns `ErrInvalid`;
tested), nor does a closed descriptor (`file already closed`; tested).
P8. **Broken stdout.** A pipe with no reader on fd 1 raises `SIGPIPE`: an exit by signal, not a
panic (not a counterexample by the skill's rules).
P9. **Concurrency / re-entrancy.** Each call takes its own `pp` from a `sync.Pool`; `(*File).Write`
serializes on the descriptor's lock; an `Error()` calling `Println` re-entrantly uses another `pp`.
P10. **Empty operand list.** `Println()` prints a newline; tested.
P11. **Cross-world entailment.** `printOk` is persistent but its pure parts are about types, and
`errAny` concludes a WP, not a pure fact of a pointer: not applicable.

## QuePaxa's operands

`printOk_str_err` (`NetPrint.lean:35`) needs, of each error, `errAny` and "not a `Formatter`", which
the net and `io.ReadFull` specs supply. In Go these errors are `*net.OpError`, `io.EOF`,
`io.ErrUnexpectedEOF` and the like: none has `Format`. The deployment never assigns `os.Stdout`.

Not tried: a machine-checked Lean counterexample (no gap found); the axioms in a context where
Perennial models `os.Stdout` (none exists yet).

No bug found in the Go code (QuePaxa's sort is of a fresh local `[]int`, its prints of plain
errors).
