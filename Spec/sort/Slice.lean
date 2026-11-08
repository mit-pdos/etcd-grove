/-
`sort.Slice(x, less)` on an `[]int64` slice `s` (names-only in Perennial: it swaps through
reflection, `reflectlite.Swapper(x)`), with a `less(i, j)` that, on indices of `s` and the slice at
any permutation of its contents, returns some boolean and keeps the slice and a resource `P`: it
returns with the slice at a permutation of its contents. True of Go (`sort/slice.go`):

    func Slice(x any, less func(i, j int) bool) {
        rv := reflectlite.ValueOf(x)
        swap := reflectlite.Swapper(x)
        length := rv.Len()
        limit := bits.Len(uint(length))
        pdqsort_func(lessSwap{less, swap}, 0, length, limit)
    }

`pdqsort_func` calls `less` and `swap` only on indices in `[0, length)`, and a swap permutes the
slice, so `less` sees it at a permutation of its contents and the slice ends at one. Stated for
the `[]int64` slices of its one caller (the mvcc tester's `writer.genLease`, which sorts a map's
keys: `examples/mvccrand`); the order `less` defines is not stated (the caller needs only the
permutation).

No proof: not assumed either (no axiom); the linked results that reach it take it as a
hypothesis (`etc/link-lean-first-mvccrand.txt`, `sort_Slice: ?`). Lean-first.
-/
module

public import Perennial.Proof.sort

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- See the file header. -/
abbrev sort.Slice.spec : Prop :=
  ∀ (s : GoSlice) (xs : List w64) (less : GoFunc) (P : IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.sort ∗ s ↦* xs ∗ P ∗
      □ (∀ (i j : w64) (ys : List w64) (Φ : val → IProp GF),
        ⌜0 ≤ sint.Z i ∧ sint.Z i < sint.Z s.len ∧ 0 ≤ sint.Z j ∧ sint.Z j < sint.Z s.len ∧
          ys.Perm xs⌝ -∗
        s ↦* ys -∗ P -∗ (∀ b : Bool, s ↦* ys -∗ P -∗ Φ #b) -∗
        WP (App (App (Val #less) (Val #i)) (Val #j)) {{ Φ }}) }}
    (App (App (Val (@! _root_.Perennial.sort.Slice'))
      (Val #(interface.mkOk (go.GoType.SliceType go.int64) #s))) (Val #less))
  {{ RET #(); ∃ ys : List w64, s ↦* ys ∗ P ∗ ⌜ys.Perm xs⌝ }}

end spec

end EtcdGrove
end Perennial
