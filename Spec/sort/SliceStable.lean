/-
`sort.SliceStable(x, less)` (names-only in Perennial: it swaps through reflection,
`reflectlite.Swapper(x)`), on a slice `s` of a slice type `S` (passed as `any`) holding `xs`, with a
`less(i, j)` that, on indices of `s` and the slice at any permutation of its contents, returns
whether `R` holds of the elements at `i` and `j` and keeps the slice and a resource `P`, for a
strict weak order `R`: it returns with the slice at a permutation of its contents that is sorted
for `R`. (Not stated: the stability, the order kept among `R`-equivalent elements.) The trust
boundary: an axiom, `Proof/sort/SliceStable.lean`.

Its caller: structured-merge-diff's `value.FieldList.Sort` (`value/fields.go`:
`sort.SliceStable(f, func(i, j int) bool { return f[i].Name < f[j].Name })`), which sorts the key
fields of an associative list's path elements. Lean-first (2026-11-19, notes/smd-robustness.md).

True of Go (`sort/slice.go`, `sort/zsortfunc.go`, go1.27):

    func SliceStable(x any, less func(i, j int) bool) {
        rv := reflectlite.ValueOf(x)
        swap := reflectlite.Swapper(x)
        stable_func(lessSwap{less, swap}, rv.Len())
    }

`x` is a slice (`Swapper` panics otherwise; here its dynamic type is `S`, a slice type);
`stable_func` (insertion sorts of blocks of 20, then `symMerge`s) calls `less` and `swap` only on
indices in `[0, len)`, and a swap permutes the slice, so `less` sees it at a permutation of its
contents; it sorts the slice for any `less` that is a strict weak order on the elements (sort's
documented requirement), so the result is a sorted permutation. The length bound keeps its index
arithmetic (`blockSize *= 2`, `a + 2*blockSize`) far from overflowing.
-/
module

public import Perennial.Proof.sort.Base
public import Perennial.Proof.slices.SortBasics

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
abbrev sort.SliceStable.spec : Prop :=
  ∀ {E : Type} [ZeroVal E] [TypedPointsto (GF := GF) E] {Et : go.GoType}
    [IntoValTyped (GF := GF) E Et] {S : go.GoType} [S ↓u go.SliceType Et]
    (R : E → E → Prop) (s : GoSlice) (xs : List E) (less : GoFunc) (P : IProp GF),
    _root_.Perennial.slices.StrictWeakOrder R →
    {{ isPkgInit (PROP := IProp GF) pkg_id.sort ∗ s ↦* xs ∗ P ∗ ⌜xs.length ≤ 2 ^ 62⌝ ∗
        □ (∀ (i j : w64) (ys : List E) (yi yj : E) (Φ : val → IProp GF),
          ⌜ys.Perm xs ∧ ys[(sint.Z i).toNat]? = some yi ∧ ys[(sint.Z j).toNat]? = some yj ∧
            0 ≤ sint.Z i ∧ 0 ≤ sint.Z j⌝ -∗
          s ↦* ys -∗ P -∗ (∀ b : Bool, ⌜b = true ↔ R yi yj⌝ -∗ s ↦* ys -∗ P -∗ Φ #b) -∗
          WP (App (App (Val #less) (Val #i)) (Val #j)) {{ Φ }}) }}
      (App (App (Val #(functions _root_.Perennial.sort.SliceStable []))
        (Val #(interface.mkOk S #s))) (Val #less))
    {{ RET #(); ∃ ys : List E, s ↦* ys ∗ P ∗ ⌜ys.Perm xs⌝ ∗
        ⌜∀ (k l : Nat) (yk yl : E), ys[k]? = some yk → ys[l]? = some yl → k < l → ¬ R yl yk⌝ }}

end spec

end EtcdGrove
end Perennial
