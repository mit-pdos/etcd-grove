/-
# `sort.StringSlice.Sort`: a trust-boundary spec (batch 3c)

**Users.** The lessor's `Revoke` (`lessor.go:348`: `sort.StringSlice(keys).Sort()`, the lease's
keys in the same order on every member). Perennial translates `sort.StringSlice`'s type but proves
none of its methods.

**Why it is true of Go's `sort`.** `x.Sort()` is `sort.Sort(x)` over `StringSlice`'s `Len`, `Less`
(`x[i] < x[j]`, Go's byte-wise string order: a strict weak order) and `Swap`: Perennial's
`sort.Sort.spec` gives a permutation in ascending order, the statement Perennial's own
`sort.Strings.spec` has for the same sort of a `[]string` (through `slices.Sort`), with the same
`2^62` bound (the heapsort fallback's index arithmetic). Provable from Perennial's `sort.Sort.spec`
once `StringSlice`'s three methods have specs (`notes/perennial-changes.md`); `specs-ref`'s
`Spec/sort/StringSlice__Sort.lean` stated it the same way.
-/
module

public import Perennial.Spec.sort.Strings

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace GoSort

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : _root_.Perennial.sort.Assumptions]

/-- **Sort a `[]string` in place**: a permutation, ascending (`GoStringLe`). -/
def StringSlice.Sort.spec : Prop :=
  ∀ (x : GoSlice) (xs : List GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.sort ∗ x ↦* xs ∗ ⌜xs.length ≤ 2 ^ 62⌝ }}
    (App (Val (x @!! _root_.Perennial.sort.StringSlice.ty @!! go!"Sort")) (Val #()))
  {{ (xs' : List GoString), RET #(); x ↦* xs' ∗ ⌜xs.Perm xs'⌝ ∗
      ⌜∀ (i j : Nat) (xi xj : GoString), xs'[i]? = some xi → xs'[j]? = some xj → i < j →
        go.GoStringLe xi xj⌝ }}

end spec

end GoSort
end EtcdGrove
end Perennial
