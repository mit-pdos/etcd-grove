/-
# `sort.Sort` with a `Less` that answers anything: a trust-boundary spec (batch 3c)

Perennial proves `sort.Sort` (`Perennial/Spec/sort/Sort.lean`) only for a sorter whose `Less`
agrees with a fixed strict weak order (`isSorter`). etcd's lessor sorts its leases by remaining
time (`leasesByExpiry.Less` compares two `Remaining()` reads of the clock, `lease.go:134`:
`lessor.Leases`, `lessor.Promote`), so no order fits.

**Assumed, and why it is true of Go's `sort`.** Go's `sort.Sort` (`pdqsort` and its helpers,
`zsortinterface.go`) bounds every index it passes to `Less` and `Swap` by the slice's bounds
(`a`, `b`, `length`, computed from `Len()` and the recursion's ranges), never by `Less`'s answers,
and only `Swap` mutates: with any `Less`, every call stays in range and the result is a
permutation; **no order is claimed** (with an inconsistent `Less` there is none). The `2^62` bound is
the same as Perennial's `sort.Sort.spec` (the heapsort fallback's `2*root+1` overflows `int` past
it). `specs-ref`'s `Spec/sort/SortAnyLess.lean` (the lease-read plan, S2, 2026-10-31) stated the
same, with a 1200-element sort test of an inconsistent `Less`; to be proved in Perennial
(`notes/perennial-changes.md`).

Namespace `GoSort` (the Go package `sort`; `Sort` is Lean's keyword).
-/
module

public import Perennial.Spec.sort.Sort

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

/-- **The `sort.Interface` `x` holds a list** by `own` (persistent), its `Less` answering anything:
`Len` and `Swap` as Perennial's `isSorter`, `Less(i, j)` (indices of the list) some boolean. -/
def sorterAny {E : Type} (x : GoInterfaceOk) (own : List E → IProp GF) : IProp GF :=
  iprop(
    □ (∀ l : List E,
      {{ own l }} (App (Val #(methods x.ty go!"Len" x.v)) (Val #()))
      {{ RET #(W64 l.length); own l }}) ∗
    □ (∀ (l : List E) (i j : w64) (a b : E),
      ⌜0 ≤ sint.Z i ∧ 0 ≤ sint.Z j ∧ l[sint.nat i]? = some a ∧ l[sint.nat j]? = some b⌝ -∗
      {{ own l }} (App (App (Val #(methods x.ty go!"Less" x.v)) (Val #i)) (Val #j))
      {{ (r : Bool), RET #r; own l }}) ∗
    □ (∀ (l : List E) (i j : w64) (a b : E),
      ⌜0 ≤ sint.Z i ∧ 0 ≤ sint.Z j ∧ l[sint.nat i]? = some a ∧ l[sint.nat j]? = some b⌝ -∗
      {{ own l }} (App (App (Val #(methods x.ty go!"Swap" x.v)) (Val #i)) (Val #j))
      {{ RET #(); own ((l.set (sint.nat i) b).set (sint.nat j) a) }}))

/-- **`sort.Sort(x)` for any `Less`**: a list of at most `2^62` elements ends a permutation of
itself (no order claimed). -/
def Sort.anyLessSpec : Prop :=
  ∀ (E : Type) (x : GoInterfaceOk) (own : List E → IProp GF) (l : List E),
  {{ isPkgInit (PROP := IProp GF) pkg_id.sort ∗ sorterAny x own ∗ own l ∗ ⌜l.length ≤ 2 ^ 62⌝ }}
    (App (Val (@! _root_.Perennial.sort.«Sort»)) (Val #(interface.ok x)))
  {{ (l' : List E), RET #(); own l' ∗ ⌜l.Perm l'⌝ }}

end spec

end GoSort
end EtcdGrove
end Perennial
