# Axiom review: `math/rand`'s `NewSource`, `New` and `(*rngSource).Int63`

Reviewed 2026-11-25 by the `axiom` skill (an independent reviewer), in the worktree
`/shared/etcd-grove-mathrand` (branch `dsv-fix4`) at `a28755b089`; Perennial `fce59af75`; Go at the
pinned toolchain go1.27.3 (`src/math/rand/rand.go`, `rng.go`).

## The axioms

In `Dsverify/Proof/math/rand/`, over the vocabulary of `RngDefs.lean`:

- `rngTok p : IProp GF`, an `opaque` (its default value `True` is invisible: `rfl` and `unfold` both
  fail on `rngTok p = iprop(True)`, checked in a scratch file);
- `isRngSource src := ∃ p, ⌜src = interface.mkOk (*rngSource) #p⌝ ∗ rngTok p`;
- `ownRngRand r := ∃ p v, r ↦□ v ∗ ⌜v.src' = interface.mkOk (*rngSource) #p⌝ ∗ rngTok p`.

The three axioms:

- `math.rand.NewSource.wp_proof` (`NewSource.lean`): `∀ seed, {{ isPkgInit math.rand }} NewSource
  seed {{ src, RET src; isRngSource src }}`;
- `math.rand.New.wp_proof` (`New.lean`): `∀ src, {{ isPkgInit math.rand ∗ isRngSource src }} New src
  {{ r, RET r; ownRngRand r }}`;
- `math.rand.rngSource.Int63.wp_proof` (`rngSource__Int63.lean`): `∀ p, {{ rngTok p }} p.Int63()
  {{ x, RET x; rngTok p ∗ ⌜0 ≤ sint.Z x⌝ }}`.

Their consumer, `RandsLinked.lean`, proves `(*Rand).Intn` over `ownRngRand` from the translated
bodies (`Intn` → `Int31n`/`Int63n` → `Int31`/`Int63` → `r.src.Int63()` by interface dispatch → the
`Int63` axiom), and `hyps_holds : math.rand.Hyps GF`. `#print axioms hyps_holds`: `propext`,
`Classical.choice`, `Quot.sound` and the three axioms, nothing else.

Perennial's translation (`Perennial/Code/math/rand.toml`) has `NewSource`, `New`, the `rngSource`
methods, `(*Rand).Seed`/`Read`/`Uint64` names only ("a call of one is stuck"); only the integer
`Rand` methods and the runtime source are translated.

Claims, in plain words: `NewSource` never panics and gives an exclusive token of a `*rngSource`;
`New` of such a source never panics and gives a `*Rand` whose `src` field is that source and never
changes, with the token moved in; `Int63` with the token never panics and returns a non-negative
value.

## Verdict: **survives** (with conditions on future specs, below)

## The Go code (go1.27.3)

- `NewSource(seed)` = `newSource(seed)`: `var rng rngSource; rng.Seed(seed); return &rng` (the
  docstring of `NewSource.lean` says `new(rngSource)`: equivalent, a fresh escaping allocation).
  `rngSource.Seed`: `seed % int32max` (no panic, also for `MinInt64`), sign fix, `0` → `89482311`,
  `seedrand` divides by constants, indices `i ∈ [0, rngLen)` into `vec` and `rngCooked`. No panic for
  any seed; touches only `rng` and reads the constant table `rngCooked`.
- `New(src)`: `s64, _ := src.(Source64); return &Rand{src: src, s64: s64}`: comma-ok assertion,
  allocation, no panic.
- `(*rngSource).Int63` = `int64(rng.Uint64() & rngMask)`, `rngMask = 1<<63 - 1`: non-negative.
  `Uint64` decrements `tap`/`feed`, wraps them into `[0, rngLen)` and indexes `vec`: in-range when
  run sequentially, writes only the source's own state.
- `(*Rand).Int63` = `r.src.Int63()` (not `s64`), so `Intn` reaches only the source's `Int63`.

## Attacks tried

1. **False pure fact (`0 ≤ Int63`).** `int64(x & (1<<63-1))` has bit 63 clear. Scratch test: seeds
   `0, -1, 2^31-1, MinInt64, MaxInt64`, 1000 draws each of `Int63` and `Intn(3)`: never negative.
2. **Missing premise (a panic of `NewSource`/`New`/`Int63`).** None on any path (above). The zero
   `Rand` (`var z rand.Rand; z.Intn(3)`) panics (nil dereference: test output below), but
   `ownRngRand` requires `v.src' = mkOk (*rngSource) p` with a token, which only `NewSource` gives:
   the zero value has no `ownRngRand`.
3. **Duplicating the token / concurrent use.** Real Go panics: 8 goroutines calling `Intn(2)` on one
   `rand.New(rand.NewSource(42))` give `runtime error: index out of range [-1]` (in `Uint64`:
   `rng.tap` read again after another goroutine's decrement), 20/20 runs. The proof cannot reach it:
   `rngTok` is opaque, so not duplicable or persistent; the triples return it once; the call of
   `Int63` is not atomic, so the token cannot sit in an invariant opened around it (a lock that the
   Go code also takes is the only way to share, and then Go is safe too). Two `NewSource` calls
   yielding the same `p` (the axiom does not state freshness) gives nothing: two tokens of one `p`
   contradict nothing, since no law of `rngTok` makes it exclusive in the logic either; the
   interpretation `rngTok p := p ↦ (rngSource state)` with Go's fresh allocations satisfies all three
   triples.
4. **Two `Rand`s sharing a source.** `New` consumes `isRngSource`, so a second `New(src)` needs a
   second token (unavailable). A Go copy `r2 := new(rand.Rand); *r2 = *r` (legal outside the package)
   is provable (loads from `r ↦□ v`), and the proof may move the token from `ownRngRand r` into a new
   `ownRngRand r2`; but then `r` has no token: the two are used sequentially, which Go allows.
5. **Persistent `r ↦□ v` vs Go writing `*Rand`.** Go writes a `Rand` only in `(*Rand).Seed`
   (`r.readPos = 0`), `(*Rand).Read` (`readVal`, `readPos`) and by a whole-struct assignment from a
   client (`*r = rand.Rand{}`, which would make `src` nil and the next `Intn` panic). The first two
   are names only (stuck, no spec anywhere in `Dsverify/`), and the store of the third needs a full
   `r ↦ _`, which `↦□` cannot give. So no proof can make `v` stale. (`swiftpaxos/client/buffer.go:105`
   calls `c.rand.Read(val)` in `Loop`, which no verified result reaches: the swiftnet proofs use
   `Write`/`Read`/`Connect`, and `NewBufferClient` drops the `Rand`'s token after storing it.)
6. **The `Source64` assertion.** `New` sets `s64` to the same `*rngSource`; the axiom says nothing of
   `v.s64'`, and `Intn`'s path does not read it. A future `(*Rand).Uint64` proof would dispatch through
   `s64` to `(*rngSource).Uint64` (names only): needs its own axiom over the same `rngTok`.
7. **`Seed` interplay.** The package-level `Seed` (axiom `Seed.lean`, reviewed in `math-rand-seed.md`)
   acts on the global generator only, never on a `NewSource` source (with `randseednop=0` it would
   swap in a fresh `lockedSource` of its own `rngSource`). `(*Rand).Seed` is names only.
8. **Package init.** `NewSource`/`New` ask `isPkgInit math.rand` and return nothing of it; `Int63`
   asks nothing, and Go's reads no package variable (`rngCooked` is read only by `Seed`, during
   `NewSource`, and is a constant table).
9. **Cross-world entailment.** No entailment from bare `↦□` cells to a pure fact about an opaque
   function: `rngTok` is not obtainable from heap cells, and the only pure facts are about the
   values in the post (`v.src'`, `x`). Not applicable.
10. **Callers.** rabia (`consensus.go:349-353`: `Coin.Intn(2)`; `ResetCommonCoin` replaces `Coin` by
    a fresh `New(NewSource(42))`, dropping the old token) and swiftpaxos (`buffer.go:57-58`,
    `Intn(100)` in `randomTrue`): both use the abstract `math.rand.Hyps` tokens, so they rely on
    nothing beyond the three triples.

## Conditions

- A future spec of `(*Rand).Seed` or `(*Rand).Read` must not be stated over `ownRngRand`: both
  write the `Rand` (`readPos`, `readVal`), which `ownRngRand`'s persistent `r ↦□ v` says never
  changes. They would need a variant owning `r ↦ v`.
- A future axiom of another `rngSource` method (`Uint64`, `Seed`) must take and return the same
  `rngTok p`, never a persistent or duplicable form of it.
- `rngTok` must stay opaque with no added law (e.g. no `Persistent`/`Timeless`-style duplication
  instance).

## Evidence (scratch, not committed)

Go test at go1.27.3, `/shared/tmp/mrrev/gotest` (removed):

    === RUN   TestConcurrent
    panic: runtime error: index out of range [-1]
    20/20 runs panicked
    === RUN   TestEdge
    zero Rand: runtime error: invalid memory address or nil pointer dereference
    PASS

Lean: `rngTok p = iprop(True)` fails by `rfl` and by `unfold`; `#print axioms
Perennial.math.rand.rng.hyps_holds` lists Lean's three and the three axioms.

Not tried: a Lean counterexample (no gap found); behaviour under `GODEBUG` settings (none of these
three functions reads one).
