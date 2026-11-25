# Axiom review: `math/rand.Seed` (`math.rand.Seed.wp_proof`)

Reviewed 2026-11-25 by the `axiom` skill (an independent reviewer), in the worktree
`/shared/etcd-grove-mathrand` (branch `dsv-fix4`) at `a28755b089`; Perennial `fce59af75`; Go at the
pinned toolchain go1.27.3 (`src/math/rand/rand.go`, `src/internal/godebug/godebug.go`,
`src/internal/godebugs/table.go`).

## The axiom

`Perennial.math.rand.Seed.wp_proof : math.rand.Seed.spec` (`Dsverify/Proof/math/rand/Seed.lean`),
the triple in `Dsverify/Proof/math/rand/Spec.lean`:

    ∀ seed : w64,
      {{ isPkgInit pkg_id.math.rand }} @! math.rand.Seed #seed {{ RET #(); True }}

Claims, in plain words: `Seed` has no precondition beyond the package's init fact (persistent, not
consumed), never panics or gets stuck, returns, and (frame rule) changes nothing any proof owns or
any invariant describes; in particular Perennial's `isInit` invariant of `globalRandGenerator`
(`nil`, or a `Rand` over two `*runtimeSource`s, `Perennial/Proof/math/rand/Base.lean`) stays true.
The file header's argument: Go's `Seed` is a no-op unless `GODEBUG` makes `randseednop` `"0"`, and
the deployment does not (an **environment claim**).

Users: gryff's `NewReplica` (`examples/dsverify/gryff/src/gryff/tupaq.go:157`, through
`gryff.lib.RandSeedHyp`, `Dsverify/Proof/gryff/Lib/RandHyps.lean`, into `gryffnet`'s
`TopLevelRobustness`), QuePaxa's proxy (`examples/dsverify/quepaxa/replica/src/proxy.go:221`,
through its own copy of the triple, `Dsverify/Proof/raxos/Hyp.lean:121`). Both programs also call
the package-level `rand.Intn` (Perennial's proofs over `isInit`).

## The Go code (go1.27.3, rand.go:400-430)

`Seed(seed)`: `if randseednop.Value() != "0" { return }`; otherwise `IncNonDefault`, then re-seed
the global generator if it is already over a `lockedSource`, or else `CompareAndSwap` it to a fresh
`New(new(lockedSource))` seeded with `seed` (retrying on a lost race). `randseednop` is listed in
`godebugs.All` (`table.go:61`, `Changed: 24, Old: "0"`), so `Setting.Value` cannot hit its
"not listed" panic (`godebug.go:160`). Its default is `"1"` (no-op) for a main module declaring
`go 1.24` or later; both kits' `go.mod` (and `examples/go.mod`) declare `go 1.27`, and no `godebug`
line or `//go:debug` directive appears under `examples/`.

## Verdict: **survives with conditions**

Conditions (environment claims, outside the Lean statement):

1. the process does not run with `GODEBUG` containing `randseednop=0` (the robust harness passes
   `os.Environ()` through to every machine's process, `examples/lib/robust/proc.go:31`,
   `root.go:78`: the runner's environment must not set it);
2. the main module of each deployed binary declares `go >= 1.24` and has no `godebug randseednop=0`
   line or `//go:debug randseednop=0` directive (true at this revision).

Under them `Seed` is exactly `return` after a non-panicking `Value()` read. Violating them gives no
counterexample either (attack 2), only a model that is unfaithful in a way no Go run can exhibit.

## Attacks tried

1. **A missing premise (Seed panics).** Paths to a panic: `Setting.Value`'s unlisted-name panic
   (excluded: listed); `runtimeSource.Seed`'s "internal error" panic (unreachable: `Seed` never
   calls `orig.Seed` unless `orig.src` is a `*lockedSource`; a `runtimeSource` generator is replaced,
   not re-seeded); unbounded recursion on repeated lost CAS (only under `randseednop=0`, and
   each retry follows another goroutine's successful CAS, which makes `orig` a `lockedSource` Rand,
   so the next attempt re-seeds and returns). No panic in any setting. Measured (scratch program, 8
   goroutines x 200000 iterations mixing `Seed`, `Intn`, `Int63n`, `Int31n`, `-race`, go1.27.3) under
   `GODEBUG` unset, `randseednop=0`, `randseednop=0,randautoseed=0`, `randautoseed=0`,
   `randseednop=junk`: every run exits 0, no race report, every `Intn(5)` in range. (Unset: `Seed(42)`
   then `Intn` gives varying values, confirming the no-op; `randseednop=0`: deterministic.)
2. **Breaking Perennial's global-generator invariant (`randseednop=0`).** Then Go's `Seed` swaps in a
   `lockedSource` generator, so `isInit`'s "`nil` or `isRuntimeRand`" is false of the real heap and
   the frame rule's "nothing changed" is false. But no Go program can turn this into a panic the
   proof excludes: the global generator is unexported, read only by the top-level functions through
   `globalRand`; the translated ones (`Int63`, `Int31`, `Int63n`, `Int31n`, `Intn`) only call `Int63`
   on it (through the same `Rand` methods), and every sequence of `lockedSource.Int63` results lies
   in `[0, 2^63)`, a sequence the model's arbitrary `runtime_rand` (masked) also produces. Perennial's
   specs claim only ranges, no values, so no proof can rule out a branch Go takes on a seeded value.
   This is the same argument `TrustedCode/math/rand.lean` makes for `randautoseed=0`, whose docstring
   already names the `randseednop=0` case. So the condition is a faithfulness condition, not a
   soundness gap exhibitable by a panicking program.
3. **Concurrency.** Go documents package-level `Seed` as safe for concurrent use (atomic pointer,
   `lockedSource` mutex; `Rand.Seed` on the global takes `lockedSource.seedPos` under the lock).
   The triple consumes nothing exclusive, so a proof may call it from any number of threads, as Go
   allows (measured, `-race`, above).
4. **Ordering with the generator's first use.** `Seed` before any `Intn` (gryff, QuePaxa: in
   constructors), after, or interleaved: under the conditions no effect; without them, attack 2.
5. **Too much ownership / persistent facts.** The post is `True`; the precondition persistent and
   kept. Nothing to duplicate or contradict. Not applicable.
6. **Cross-world entailment.** No pure conclusion, no opaque function of a pointer: not applicable.
7. **Inconsistency (`⊢ False`).** `@! math.rand.Seed` resolves through the context's opaque
   `functions` table (names only); no lemma fixes its body, so the triple cannot be refuted in a
   fixed context. As for every names-only trust-boundary axiom here (`os-signal.md`, attack 8), it
   is stated for every Go context, satisfiable only in those where the name resolves to Go's code.

Not tried: a Lean counterexample (no Go panic found to build it on).

## Remarks

- `Dsverify/Proof/math/rand/Spec.lean`'s docstring of `math.rand.Seed.spec` says "(it reseeds the
  locked global source; ...)": that is Go's behaviour only under `randseednop=0`, the case the axiom
  excludes; the header of `Seed.lean` is the accurate one. Worth aligning (documentation only).
- The environment claim has no Lean counterpart: the `Robust` statement does not mention
  `GODEBUG`. Making it explicit in the deployment (the harness clearing or fixing `GODEBUG` for the
  machines' processes, or a `godebug randseednop=1` line in the kits' `go.mod`) would turn condition 1
  into a property of the deployed program instead of the runner's environment.
- Retiring it: once Perennial translates `Seed` (needs `internal/godebug`'s `Setting.Value`, or a
  trusted model of `Seed` with `randseednop` at its default, as `globalRand`'s model does for
  `randautoseed`), the spec is provable from the `return` branch.

## Proposed restatement

None needed.

No bug found in the verified Go code (gryff's and QuePaxa's `rand.Seed` calls are no-ops at go 1.24+,
deprecated but harmless).
