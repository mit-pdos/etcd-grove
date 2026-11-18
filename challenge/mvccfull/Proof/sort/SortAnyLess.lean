/-
The trust boundary: `sort.Sort` for a `Less` that answers anything (`Spec/sort/SortAnyLess.lean`;
the lease-read plan, S2, the user's choice, 2026-10-31). Perennial's proof (`sort.wp_Sort`) needs a
strict weak order; Go's `pdqsort` (`zsortinterface.go`: `insertionSort`, `siftDown`/`heapSort`,
`pdqsort`, `partition`, `partitionEqual`, `partialInsertionSort`, `breakPatterns`, `choosePivot`,
`median`, `medianAdjacent`, `reverseRange`) bounds every index by the slice's bounds (`j > a`,
`child+1 < hi`, `i <= j`, `i < b`, `j >= 1`, ...), never by `Less`'s answers, and only permutes by
`Swap` (`partialInsertionSort`'s left shift, bounded by `j >= 1` and not by the segment's start,
may move elements below the segment: still in the slice). Tested at go1.27.3 with a random, an
always-true, an always-false and a positional `Less`, 1200 sorts of up to 100000 elements: no
panic, each a permutation (the lease-read plan, Test). To be removed when Perennial proves it (`notes/perennial-changes.md`).
-/
module

public import Spec.sort.SortAnyLess

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : _root_.Perennial.sort.Assumptions]

axiom sort.«Sort».wp_anyLess : sort.«Sort».anyLessSpec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
