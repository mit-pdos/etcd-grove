/-
`sort.Sort` over a `sort.Interface` whose `Less` answers anything (the lease-read plan, S2,
2026-10-31; `notes/lease-read-plan.md`). Lean-first.

**The sorter, any `Less`** (`sorterAnySpec x R`): as `sorterSpec` (`Spec/sort/Sort.lean`), but
`Less(i, j)` returns some boolean, not one a fixed order determines: `lease.leasesByExpiry`'s
compares `Remaining()`, read off the clock. **`sort.Sort(x)`** then leaves the sorter holding a
permutation of its list, with no order. Perennial proves `sort.Sort` only for a `Less` that agrees
with a strict weak order (`sort.isSorter`); Go's `pdqsort` and its helpers (`zsortinterface.go`)
bound every index they pass to `Less` and `Swap` by the slice's bounds, never by `Less`'s answers,
so a `Less` that answers anything keeps the calls in range: `sort.Sort.wp_anyLess`, a trust-boundary
axiom here until Perennial proves it (`notes/perennial-changes.md`).
-/
module

public import Spec.sort.Sort

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : _root_.Perennial.sort.Assumptions]

/-- **The `sort.Interface` `x` holds a list** by `R` (persistent), its `Less` answering anything:
`Len` and `Swap` as `sorterSpec`'s, `Less(i, j)` (indices of the list) some boolean. -/
def sorterAnySpec {E : Type} (x : GoInterfaceOk) (R : List E → IProp GF) : IProp GF :=
  iprop(
    □ (∀ l : List E,
      {{ R l }} (App (Val #(methods x.ty go!"Len" x.v)) (Val #()))
      {{ RET #(W64 l.length); R l }}) ∗
    □ (∀ (l : List E) (i j : w64) (a b : E),
      ⌜0 ≤ sint.Z i ∧ 0 ≤ sint.Z j ∧ l[sint.nat i]? = some a ∧ l[sint.nat j]? = some b⌝ -∗
      {{ R l }} (App (App (Val #(methods x.ty go!"Less" x.v)) (Val #i)) (Val #j))
      {{ (r : Bool), RET #r; R l }}) ∗
    □ (∀ (l : List E) (i j : w64) (a b : E),
      ⌜0 ≤ sint.Z i ∧ 0 ≤ sint.Z j ∧ l[sint.nat i]? = some a ∧ l[sint.nat j]? = some b⌝ -∗
      {{ R l }} (App (App (Val #(methods x.ty go!"Swap" x.v)) (Val #i)) (Val #j))
      {{ RET #(); R ((l.set (sint.nat i) b).set (sint.nat j) a) }}))

instance sorterAnySpec_persistent {E : Type} (x : GoInterfaceOk) (R : List E → IProp GF) :
    Persistent (sorterAnySpec x R) := by
  unfold sorterAnySpec; infer_instance

/-- **`sort.Sort(x)` for any `Less`**: a list of at most `2^62` elements (as `sort.Sort.spec`)
ends a permutation of itself. -/
abbrev sort.«Sort».anyLessSpec : Prop :=
  ∀ (E : Type) (x : GoInterfaceOk) (R : List E → IProp GF) (l : List E),
  {{ isPkgInit (PROP := IProp GF) pkg_id.sort ∗ sorterAnySpec x R ∗ R l ∗ ⌜l.length ≤ 2 ^ 62⌝ }}
    (App (Val (@! sort.«Sort»)) (Val #(GoInterface.ok x)))
  {{ (l' : List E), RET #(); R l' ∗ ⌜l.Perm l'⌝ }}

end spec

end EtcdGrove
end Perennial
