/-
`slices.BinarySearchFunc(x, target, cmp)` (names-only in Perennial: its `slices.toml` translates the
sorts only), on a slice `x` holding `xs` read with any fraction, for a `cmp` that on every element
of `xs` and the target returns `c x` (a pure function of the element) and keeps a resource `I`,
where the signs of `c` are non-decreasing along `xs` (`xs` is sorted for the target): it returns
`(i, found)` with `i` the least index whose `c` is non-negative (`len(xs)` if none) and `found`
whether `c` is `0` there. The trust boundary: an axiom, `Proof/slices/BinarySearchFunc.lean`.

Its callers: structured-merge-diff's sorted sets and maps of path elements (`fieldpath`:
`PathElementSet.Insert`/`Has`, `PathElementMap`/`PathElementValueMap.Insert`/`Get`,
`SetNodeMap.Descend`/`Get`), whose `cmp` compares an element's path element with the target's
(`PathElement.Compare`), on members kept sorted by it. Lean-first (2026-11-19,
notes/smd-robustness.md).

True of Go (`slices/sort.go`, go1.27):

    func BinarySearchFunc[S ~[]E, E, T any](x S, target T, cmp func(E, T) int) (int, bool) {
        n := len(x)
        i, j := 0, n
        for i < j {
            h := int(uint(i+j) >> 1) // avoid overflow when computing h
            if cmp(x[h], target) < 0 { i = h + 1 } else { j = h }
        }
        return i, i < n && cmp(x[i], target) == 0
    }

It reads `x` only at indices in `[0, n)` and calls `cmp` only on those elements; the loop keeps
`c xs[k] < 0` for `k < i` and `c xs[k] ≥ 0` for `j ≤ k < n` (by monotonicity of the signs), so at
`i = j` the index is the least one with a non-negative `c`; `uint(i+j)` does not overflow (`n` is
a length).
-/
module

public import Perennial.Proof.slices.Base
public import Perennial.Proof.sort.FindBasics

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
abbrev slices.BinarySearchFunc.spec : Prop :=
  ∀ {E : Type} [ZeroVal E] [TypedPointsto (GF := GF) E] {Et : go.GoType}
    [IntoValTyped (GF := GF) E Et] {S : go.GoType} [S ↓u go.SliceType Et]
    {T : Type} (Tt : go.GoType)
    (x : GoSlice) (xs : List E) (dq : DFrac) (target : T) (cmp_code : GoFunc) (c : E → Int)
    (I : IProp GF),
    {{ isPkgInit (PROP := IProp GF) pkg_id.slices ∗ x ↦*{dq} xs ∗ I ∗
        □ (∀ (e : E), ⌜e ∈ xs⌝ -∗
          {{ I }} (App (App (Val #cmp_code) (Val #e)) (Val #target))
          {{ (r : w64), RET #r; I ∗ ⌜sint.Z r = c e⌝ }}) ∗
        ⌜∀ (k l : Nat) (ek el : E), xs[k]? = some ek → xs[l]? = some el → k < l →
          sort.signum (c ek) ≤ sort.signum (c el)⌝ }}
      (App (App (App (Val #(functions _root_.Perennial.slices.BinarySearchFunc [S, Et, Tt]))
        (Val #x)) (Val #target)) (Val #cmp_code))
    {{ (i : w64) (found : Bool), RET (PairV #i #found);
        x ↦*{dq} xs ∗ I ∗
        ⌜0 ≤ sint.Z i ∧ sint.Z i ≤ xs.length⌝ ∗
        ⌜∀ (k : Nat) (ek : E), xs[k]? = some ek → (k < sint.Z i ↔ c ek < 0)⌝ ∗
        ⌜found = true ↔ ∃ ei : E, xs[(sint.Z i).toNat]? = some ei ∧ c ei = 0⌝ }}

end spec

end EtcdGrove
end Perennial
