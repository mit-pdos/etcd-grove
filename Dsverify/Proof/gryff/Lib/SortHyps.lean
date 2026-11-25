/-
**Hypothesis: `sort.Slice`** (notes/dsv-gryff.md, "Hypotheses"). `gryffcommon.ShortCircuit` sorts a
`[]int32` with `sort.Slice(sl, func(i, j int) bool { return sl[i] < sl[j] })`. Perennial
`7b2259a12` translates `sort.Slice` names only (`Perennial/Code/sort.toml` translates `sort.Sort`'s
pdqsort over a `sort.Interface`, not `Slice`, which goes through `internal/reflectlite`'s
`Swapper`); the lab proved this spec over its own trusted insertion-sort model
(`Harness/Code/sort_extra.lean`), which is not allowed here. So it is a premise (a `Prop` class
taken as a section variable up to the top-level statement; no instance anywhere).

Why it is true of Go's `sort.Slice` (`sort/slice.go`, `zsortfunc.go`): `x` is a slice (here a
`[]int32`), so `reflectlite.Swapper` and `ValueOf(x).Len()` do not panic; pdqsort calls
`less(i, j)` only with `0 ≤ i, j < len` on the slice's current contents and permutes its elements
by swaps, so the slice ends a permutation of `xs` sorted by `less`. `less` here is `slt` on the
elements, a strict total order on `int32` values: equal elements are equal values, so the sorted
permutation is unique, `xs.mergeSort sle`. `less` may be called any number of times (on any
contents the sort reaches), each call given the slice and the frame `F` and returning them
(`lessOk`); nothing else is touched.


**dsv-fix4** (mit-pdos/etcd-grove#49 fix 4): no longer a statement premise: the top-level proof builds the instance from the trust-boundary axiom `sort.Slice.wp_proofInt32Lt` (`Dsverify/Proof/sort/Slice.lean`; review `notes/axiom-review/dsv-fix4/sort-slice.md`).
-/
module

public import Dsverify.Proof.gryff.Replica2.Specs

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.gryff.replica2

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net
open Perennial.gryff.model (sle slt)

section
variable [GooseExts] [GooseSemantics] [GooseInterp] [GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS .hasLC GF] [sem : go.Semantics]

/-- `less(i, j)` compares the elements at `i` and `j` of the slice `sl` with `<` (a frame `F`). -/
def lessOk (sl : GoSlice) (F : IProp GF) (less : GoFunc) : IProp GF :=
  iprop(□ ∀ (ys : List w32) (i j : w64) (a b : w32), ⌜ys[(sint.Z i).toNat]? = some a ∧
      ys[(sint.Z j).toNat]? = some b ∧ 0 ≤ sint.Z i ∧ 0 ≤ sint.Z j⌝ -∗ sl ↦* ys ∗ F -∗
    WP (App (App (Val #less) (Val #i)) (Val #j)) {{ v, ⌜v = #(slt a b)⌝ ∗ sl ↦* ys ∗ F }})

instance lessOk_persistent (sl : GoSlice) (F : IProp GF) (less : GoFunc) :
    Persistent (lessOk sl F less) := by
  unfold lessOk; infer_instance

/-- **Hypothesis** (the file header): `sort.Slice` on a `[]int32` with a `<` comparison. -/
class SortSliceHyp (GF : BundledGFunctors) [hG : HeapGS .hasLC GF] [go.Semantics] : Prop where
  slice : ∀ (sl : GoSlice) (xs : List w32) (less : GoFunc) (F : IProp GF),
    {{ sl ↦* xs ∗ F ∗ lessOk sl F less }}
      (App (App (Val (@! sort.Slice')) (Val #(interface.mkOk (go.SliceType go.int32) #sl)))
        (Val #less))
    {{ RET #(); sl ↦* xs.mergeSort (fun a b => sle a b) ∗ F }}

end

end Perennial.gryff.replica2
