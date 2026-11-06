/-
`sort.SliceIsSorted(x, less)` (names-only in Perennial: it reads its slice through reflection,
`reflectlite.ValueOf(x).Len()`), on a slice `s` (element type `t`) and a `less(i, j)` that, on
indices of `s`, returns `lt i j` and keeps a resource `P`: it returns whether no element is `less`
than the one before it. The trust boundary: an axiom, `Proof/sort/SliceIsSorted.lean`. True of Go
(`sort/slice.go`):

    func SliceIsSorted(x any, less func(i, j int) bool) bool {
        rv := reflectlite.ValueOf(x)
        n := rv.Len()
        for i := n - 1; i > 0; i-- {
            if less(i, i-1) {
                return false
            }
        }
        return true
    }

`x` is a slice (`Len` panics on any other kind), so `n` is its length; `less` is called only on
`(i, i-1)` with `0 < i < n`, both indices of the slice, in the curried form Goose gives a call of a
function value (`App (App f i) j`); the result is `false` at the first `i` (from the end) with
`less(i, i-1)`, else `true`. Needed by bbolt's `hashMap.Init` (it panics if its page ids are not
sorted). Moved from bbolt's `internal/freelist/Lemmas/Callees.lean` (2026-11-05), where it was a
hypothesis of the linked results; the user approved it as trust-boundary assumption. Lean-first.
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
abbrev sort.SliceIsSorted.spec : Prop :=
  ∀ (t : go.GoType) (s : GoSlice) (less : GoFunc) (P : IProp GF) (lt : Nat → Nat → Bool),
  {{ P ∗ □ (∀ (i j : w64) (Φ : val → IProp GF),
        ⌜0 ≤ sint.Z i ∧ sint.Z i < sint.Z s.len ∧ 0 ≤ sint.Z j ∧ sint.Z j < sint.Z s.len⌝ -∗
        P -∗ (P -∗ Φ #(lt (sint.nat i) (sint.nat j))) -∗
        WP (App (App (Val #less) (Val #i)) (Val #j)) {{ Φ }}) }}
    (App (App (Val #(functions _root_.Perennial.sort.SliceIsSorted []))
      (Val #(interface.mkOk (go.GoType.SliceType t) #s))) (Val #less))
  {{ (b : Bool), RET #b;
      ⌜b = true ↔ ∀ i, 0 < i → i < sint.nat s.len → lt i (i - 1) = false⌝ ∗ P }}

end spec

end EtcdGrove
end Perennial
