/-
`sort.StringSlice.Sort`: the trust boundary (Perennial translates `sort.StringSlice`'s type but
none of its methods; `notes/perennial-changes.md`). Lean-first (no Rocq counterpart); the lessor's
`Revoke` sorts a lease's keys with it (`notes/leases-plan.md`, L2d).
-/
module

public import Perennial.Proof.sort

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

/-- `x.Sort()` for `x` a `sort.StringSlice` (a `[]string`): `sort.Sort(x)` over its `Len`, `Less`
(`x[i] < x[j]`, Go's byte-wise string order) and `Swap`, so the slice holds a permutation of its
strings in ascending order; the statement is Perennial's `sort.Strings.spec` (which sorts a
`[]string` the same way through `slices.Sort`), with the same bound on the length (past `2^62`
elements the heapsort fallback's index arithmetic overflows). -/
abbrev sort.StringSlice.Sort.spec : Prop :=
  ∀ (x : GoSlice) (xs : List GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.sort ∗ x ↦* xs ∗ ⌜xs.length ≤ 2 ^ 62⌝ }}
    (App (Val (x @!! _root_.Perennial.sort.StringSlice.ty @!! go!"Sort")) (Val #()))
  {{ (xs' : List GoString), RET #(); x ↦* xs' ∗ ⌜xs ≡ₚ xs'⌝ ∗
      ⌜∀ (i j : Nat) (xi xj : GoString), xs'[i]? = some xi → xs'[j]? = some xj → i < j →
        go.GoStringLe xi xj⌝ }}

end spec

end EtcdGrove
end Perennial
