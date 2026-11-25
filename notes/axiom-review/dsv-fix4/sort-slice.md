# Axiom review: `sort.Slice` on a `[]int32` with `<` (`sort.Slice.wp_proofInt32Lt`)

**Retired 2026-11-25** (branch `dsv-fix4`): no length bound; replaced by `slices.Sort` under a guard.
The triple takes a slice of any length, but past `2^62` elements pdqsort's heapsort fallback overflows
`2*root+1` (zeldovich, #18; ledger 2026-11-25, sortslice2), so it may be false in the model.
`gryffcommon.ShortCircuit` now sorts with `slices.Sort(keys)` and short-circuits the reads only while
`len(keys) <= maxShortReads` (`1 << 20`), proved over Perennial's `slices.wp_Sort`; the axiom,
`Dsverify/Proof/sort/Slice.lean` and the class `SortSliceHyp` are deleted. The review below is kept
as it was.

Reviewed 2026-11-25 by the `axiom` skill (an independent reviewer), in the worktree
`/shared/etcd-grove-mathrand` (branch `dsv-fix4`) at `a28755b089`; Perennial `fce59af75`; Go at the
pinned toolchain go1.27.3 (`src/sort/slice.go`, `zsortfunc.go`, `src/internal/reflectlite/swapper.go`).

## The axiom

`Perennial.sort.Slice.wp_proofInt32Lt` (`Dsverify/Proof/sort/Slice.lean`), verbatim the field
`slice` of the former premise `gryff.replica2.SortSliceHyp` (`Dsverify/Proof/gryff/Lib/SortHyps.lean`):

    ∀ sl xs less F,
    {{ sl ↦* xs ∗ F ∗ lessOk sl F less }}
      @! sort.Slice' #(interface.mkOk (go.SliceType go.int32) #sl) #less
    {{ RET #(); sl ↦* xs.mergeSort sle ∗ F }}

    lessOk sl F less := □ ∀ ys i j a b, ⌜ys[i]? = some a ∧ ys[j]? = some b ∧ 0 ≤ i ∧ 0 ≤ j⌝ -∗
        sl ↦* ys ∗ F -∗ WP less i j {{ v, ⌜v = #(slt a b)⌝ ∗ sl ↦* ys ∗ F }}

(`slt`/`sle`: `sint.Z` comparisons, `Dsverify/Proof/gryff/Model/Types.lean:34,36`.) Perennial
translates `sort.Slice` names only (`Perennial/Code/sort.toml` lists no `Slice`), so the call
resolves through the context's opaque function table.

Claims, in plain words: (1) `sort.Slice` does not panic on any `[]int32` (nil and empty included);
(2) it calls `less` only with in-range, non-negative indices, on contents that are a permutation of
`xs`, with the slice and `F` available; (3) it ends with the slice's `len` elements equal to `xs`
sorted ascending by signed `≤`; (4) it touches nothing but those elements (frame), and gives `F`
back.

Used by: gryff's `gryffcommon.ShortCircuit` (`examples/dsverify/gryff/src/gryffcommon/coordinator.go:230`,
`sort.Slice(keys, func(i, j int) bool { return keys[i] < keys[j] })`), through
`Dsverify/Proof/gryff/H1/Sort.lean` (`wp_sort_Slice`), instantiated in
`Dsverify/Proof/gryff/examples/gryffnet/TopLevelRobustness.lean:204`.

## Verdict: **survives** (with the generic context condition of attack 9)

## Attacks tried

1. **Panics in `sort.Slice` itself.** `Slice` (`slice.go:24-30`) panics only if `x` is not a slice
   (`reflectlite.Swapper`, `swapper.go:19`); the argument's dynamic type is fixed by the axiom to
   `[]int32` (a named slice type would be a different `go.SliceType`/named type in the translation,
   so the axiom would not apply). `Swapper` on length 0 or 1 returns a swap that panics on any call
   (`swapper.go:24-31`), but `pdqsort_func` on length < 12 is `insertionSort_func`
   (`zsortfunc.go:10-13`), whose loops do not run for `b - a ≤ 1`: no swap, no `less` call. For
   size 4, non-pointer elements, the swapper is `is[i], is[j] = is[j], is[i]` on a `[]int32` view of
   the header (`swapper.go:53-55`): bounds by `len`, never `cap`.
2. **Out-of-range or negative indices to `less`** (would escape `lessOk`'s premise). pdqsort's index
   arithmetic stays in `[a, b) ⊆ [0, len)`; instrumented in the Go test: 14,090,626 calls,
   0 out of range.
3. **The result vs Go's actual permutation.** pdqsort is unstable and its permutation depends on
   `breakPatterns` (a deterministic xorshift), but it moves elements only by `Swap`, so the result is
   a permutation of `xs` sorted by `less`. With `less = slt`, a strict total order on `int32` values
   where incomparable elements are equal values, the sorted permutation is unique, hence
   `xs.mergeSort sle`. Test: 20,000 random slices (length 0-299, many duplicates, `MinInt32`,
   `MaxInt32`, negatives) all equal `slices.Sort` of a copy; the backing array beyond `len` untouched.
4. **`less` with effects permitted by `F`.** `F` is any resource, so `less` may mutate what `F`
   owns (a call counter, `F = ∃ n, c ↦ n`) — Go's sort does not read it and the post says nothing
   about its value beyond `F`. `less` may not change `sl`'s elements across a call (it must return
   `sl ↦* ys` for the same `ys`); a write-and-restore inside `less`, or even a re-entrant
   `sort.Slice` of the same slice inside `less` followed by restoring the copy, is invisible to Go's
   pdqsort, which keeps only indices, never element values, across `less`/`Swap` calls (tested: the
   result is still sorted).
5. **`less` reading other memory or aliases.** `lessOk` quantifies over every content `ys` with `F`
   fixed, so a `less` whose result is not `slt` of `sl`'s own elements at `i`, `j` cannot prove it:
   reading another slice needs its cells in `F`, and its contents then need not agree with `sl`'s.
   A `less` reading through a variable that `F` lets it re-point (`F = ∃ s, p ↦ s`) fails the same
   way. An alias of `sl`'s cells in `F` contradicts `sl ↦* xs ∗ F` (the pre is then `False`). In
   gryff `less` reads the captured `keys` variable (`F` holds its points-to to `sl`), as Go does.
6. **A `less` that is not a strict order / panics / loops.** `lessOk` forces the returned value to be
   `slt` of the current elements, so no inconsistent comparator meets it; a `less` that panics has no
   WP; one that loops makes `sort.Slice` loop in Go too (partial correctness, no counterexample).
7. **Nil and empty slices.** `sort.Slice([]int32(nil), less)`: `any` holds a non-nil interface with
   dynamic type `[]int32` and nil data (what `interface.mkOk (go.SliceType go.int32) #sl` encodes);
   length 0, no call to `less`. Tested: returns; `less` not called. Post `[] .mergeSort = []`.
8. **Concurrency.** The pre owns `sl ↦* xs` fully, so no other thread can write the elements while
   the sort runs; `less` cannot hand them to a forked goroutine (it must give them back whole).
   Go's `sort.Slice` starts no goroutine.
9. **Inconsistency / the context.** The triple is about the opaque `functions "sort.Slice"` entry;
   no lemma fixes it, so no `⊢ False` follows in a fixed context. Like every names-only trust-boundary
   axiom of the repository, it is stated for every `GoGlobalContext`/`go.Semantics` and would be false
   in a context where `sort.Slice` resolves to a panicking body; it is satisfiable only in the
   contexts where the names resolve to Go's code (`notes/axiom-review/dsv-inits/os-signal.md`,
   attack 8). Not specific to this axiom.
10. **Cross-world entailment.** `lessOk` is persistent but concludes a WP, not a pure equation of an
    opaque function of a pointer; the post's pure content (`mergeSort`) is about the run's own cells.
    Not applicable.

Go check (scratch module, deleted; go1.27.3): nil slice with a `less` that fails the test if called,
a one-element slice, then 20,000 random `[]int32` of length 0-299 sorted through a sub-slice of a
larger array, with a `less` that counts calls, checks index ranges, writes and restores `keys[i]`,
and every 97th iteration re-entrantly sorts the slice and restores it: `PASS`,
`calls=14090626 oob=0`, results equal to `slices.Sort`, tail beyond `len` unchanged.

Not tried: a Lean counterexample (no gap found to build one on); `less` over a 32-bit `int`
(`sint.Z` of a `w64` index; the target is 64-bit, as Goose's `int`).

No bug found in the Go code (gryff's call sorts a fresh-enough local header `keys`; its `less` is
`<` on its own elements).
