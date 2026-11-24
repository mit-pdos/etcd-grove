/-
`sort.Sort` for a `Less` that answers anything, linked (`Spec/sort/SortAnyLess.lean`): the any-`Less`
proofs of `sort.Sort` and of the pdqsort helpers it calls (`Proof/sort/*AnyLess.lean`) applied to
their callees' results, with Perennial's `math.bits.Len`, `sort.nextPowerOfTwo` and
`sort.xorshift.Next`. `sort.«Sort».wp_anyLess` is the callee `lease.lessor.Leases` and bbolt's
`Tx.write` take (`=EtcdGrove.sort.«Sort».wp_anyLess` in `etc/link-lean-first-*.txt`, `etc/link_bbolt.py`).
-/
module

public import Proof.sort.SortAnyLess
public import Proof.sort.pdqsortAnyLess
public import Proof.sort.insertionSortAnyLess
public import Proof.sort.siftDownAnyLess
public import Proof.sort.heapSortAnyLess
public import Proof.sort.breakPatternsAnyLess
public import Proof.sort.order2AnyLess
public import Proof.sort.medianAnyLess
public import Proof.sort.medianAdjacentAnyLess
public import Proof.sort.choosePivotAnyLess
public import Proof.sort.reverseRangeAnyLess
public import Proof.sort.partialInsertionSortAnyLess
public import Proof.sort.partitionEqualAnyLess
public import Proof.sort.partitionAnyLess

@[expose] public section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section link
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : _root_.Perennial.sort.Assumptions]

theorem sort.insertionSort.wp_anyLess : sort.insertionSort.anyLessSpec (GF := GF) (hG := hG) :=
  sort.insertionSort.wp_proofAnyLess
theorem sort.siftDown.wp_anyLess : sort.siftDown.anyLessSpec (GF := GF) (hG := hG) :=
  sort.siftDown.wp_proofAnyLess
theorem sort.heapSort.wp_anyLess : sort.heapSort.anyLessSpec (GF := GF) (hG := hG) :=
  sort.heapSort.wp_proofAnyLess sort.siftDown.wp_anyLess
theorem sort.breakPatterns.wp_anyLess : sort.breakPatterns.anyLessSpec (GF := GF) (hG := hG) :=
  sort.breakPatterns.wp_proofAnyLess _root_.Perennial.sort.wp_nextPowerOfTwo
    _root_.Perennial.sort.xorshift.wp_Next
theorem sort.order2.wp_anyLess : sort.order2.anyLessSpec (GF := GF) (hG := hG) :=
  sort.order2.wp_proofAnyLess
theorem sort.median.wp_anyLess : sort.median.anyLessSpec (GF := GF) (hG := hG) :=
  sort.median.wp_proofAnyLess sort.order2.wp_anyLess
theorem sort.medianAdjacent.wp_anyLess : sort.medianAdjacent.anyLessSpec (GF := GF) (hG := hG) :=
  sort.medianAdjacent.wp_proofAnyLess sort.median.wp_anyLess
theorem sort.choosePivot.wp_anyLess : sort.choosePivot.anyLessSpec (GF := GF) (hG := hG) :=
  sort.choosePivot.wp_proofAnyLess sort.medianAdjacent.wp_anyLess sort.median.wp_anyLess
theorem sort.reverseRange.wp_anyLess : sort.reverseRange.anyLessSpec (GF := GF) (hG := hG) :=
  sort.reverseRange.wp_proofAnyLess
theorem sort.partialInsertionSort.wp_anyLess :
    sort.partialInsertionSort.anyLessSpec (GF := GF) (hG := hG) :=
  sort.partialInsertionSort.wp_proofAnyLess
theorem sort.partitionEqual.wp_anyLess : sort.partitionEqual.anyLessSpec (GF := GF) (hG := hG) :=
  sort.partitionEqual.wp_proofAnyLess
theorem sort.partition.wp_anyLess : sort.partition.anyLessSpec (GF := GF) (hG := hG) :=
  sort.partition.wp_proofAnyLess
theorem sort.pdqsort.wp_anyLess : sort.pdqsort.anyLessSpec (GF := GF) (hG := hG) :=
  sort.pdqsort.wp_proofAnyLess sort.insertionSort.wp_anyLess sort.heapSort.wp_anyLess
    sort.breakPatterns.wp_anyLess sort.choosePivot.wp_anyLess sort.reverseRange.wp_anyLess
    sort.partialInsertionSort.wp_anyLess sort.partitionEqual.wp_anyLess sort.partition.wp_anyLess
/-- `sort.Sort` for any `Less` (until 2026-11-21 an axiom). -/
theorem sort.«Sort».wp_anyLess : sort.Sort''.anyLessSpec (GF := GF) (hG := hG) :=
  sort.«Sort».wp_proofAnyLess sort.pdqsort.wp_anyLess _root_.Perennial.math.bits.wp_Len

end link

end EtcdGrove
end Perennial
