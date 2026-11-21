/-
`sort.swapRange` over a `sort.Interface` (the sorter of `Spec/sort/Sort.lean`): the sorter ends
holding `swapRangeM` of its list (`Proof/sort/StableModel.lean`), the code's own steps; what that
computes is `Proof/sort/StableCorrect.lean`'s. One of `sort.Stable`'s callees (`Spec/sort/Stable.lean`).
-/
module

public import Spec.sort.Sort
public import Proof.sort.StableModel

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

/-- `swapRange(data, a, b, n)`: `Swap(a + i, b + i)` for `i < n`. -/
abbrev sort.swapRange.spec : Prop :=
  ∀ (E : Type) (x : GoInterfaceOk) (R : List E → IProp GF) (lt : E → E → Bool) (l : List E)
    (a b n : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.sort ∗ sorterSpec x R lt ∗ R l ∗
      ⌜0 ≤ sint.Z a ∧ 0 ≤ sint.Z b ∧ 0 ≤ sint.Z n ∧ sint.Z a + sint.Z n ≤ l.length ∧
        sint.Z b + sint.Z n ≤ l.length ∧ l.length ≤ 2 ^ 62⌝ }}
    (App (App (App (App (Val (@! sort.swapRange)) (Val #(GoInterface.ok x))) (Val #a)) (Val #b))
      (Val #n))
  {{ RET #(); R (stableModel.swapRangeM l (sint.nat a) (sint.nat b) (sint.nat n)) }}

end spec

end EtcdGrove
end Perennial
