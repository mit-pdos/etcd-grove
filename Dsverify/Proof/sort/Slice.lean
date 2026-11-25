/-
**Trust-boundary axiom** (dsv-fix4, mit-pdos/etcd-grove#49 fix 4): `sort.Slice(x, less)` on a
`[]int32` with the comparison `less(i, j) = x[i] < x[j]` (gryff's `gryffcommon.ShortCircuit`:
`sort.Slice(sl, func(i, j int) bool { return sl[i] < sl[j] })`) leaves the slice sorted ascending:
the statement premise `gryff.replica2.SortSliceHyp` until dsv-fix4, its field `slice` verbatim
(`Dsverify/Proof/gryff/Lib/SortHyps.lean`, which defines `lessOk`). Perennial translates
`sort.Slice` names only (`Perennial/Code/sort.toml`: it goes through `internal/reflectlite`'s
`Swapper`, which has no semantics).
Why it is true of Go's `sort.Slice` (`sort/slice.go`, `zsortfunc.go`): `x` is a slice, so
`reflectlite.Swapper` and `ValueOf(x).Len()` do not panic; pdqsort calls `less(i, j)` only with
`0 ≤ i, j < len` on the slice's current contents and permutes its elements by swaps, so the slice
ends a permutation of `xs` sorted by `less`. `less` here is `<` on the elements (`lessOk`: on any
contents `ys` the sort reaches, given the slice and the frame `F` back, it returns `slt a b` of the
elements at `i` and `j`), a strict total order on `int32` values, so the sorted permutation is
unique, `xs.mergeSort sle`. Nothing else is touched. Review:
`notes/axiom-review/dsv-fix4/sort-slice.md`.
-/
module

public import Dsverify.Proof.gryff.Lib.SortHyps

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open Perennial.gryff.model (sle slt)
open Perennial.gryff.replica2 (lessOk)

section ax
variable [GooseExts] [GooseSemantics] [GooseInterp] [GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS .hasLC GF] [go.Semantics]

/-- **Trust-boundary axiom** (the file header). -/
axiom sort.Slice.wp_proofInt32Lt : ∀ (sl : GoSlice) (xs : List w32) (less : GoFunc) (F : IProp GF),
    {{ sl ↦* xs ∗ F ∗ lessOk sl F less }}
      (App (App (Val (@! sort.Slice')) (Val #(interface.mkOk (go.SliceType go.int32) #sl)))
        (Val #less))
    {{ RET #(); sl ↦* xs.mergeSort (fun a b => sle a b) ∗ F }}

end ax

end Perennial
