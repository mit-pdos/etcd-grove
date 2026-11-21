/-
`sort.insertionSort` over a `sort.Interface` (the sorter of `Spec/sort/Sort.lean`): the sorter ends
holding `insertionSortM` of its list (`Proof/sort/StableModel.lean`), the code's own steps; what that
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

/-- `insertionSort(data, a, b)` (this repository's spec, the steps of the code; Perennial's
`sort.insertionSort.spec` states only a sorted permutation, which is not enough for `Stable`). -/
abbrev sort.insertionSort.spec : Prop :=
  ∀ (E : Type) (x : GoInterfaceOk) (R : List E → IProp GF) (lt : E → E → Bool) (l : List E)
    (a b : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.sort ∗ sorterSpec x R lt ∗ R l ∗
      ⌜0 ≤ sint.Z a ∧ sint.Z a ≤ sint.Z b ∧ sint.Z b ≤ l.length ∧ l.length ≤ 2 ^ 62⌝ }}
    (App (App (App (Val (@! sort.insertionSort)) (Val #(GoInterface.ok x))) (Val #a)) (Val #b))
  {{ RET #(); R (stableModel.insertionSortM lt l (sint.nat a) (sint.nat b)) }}

end spec

end EtcdGrove
end Perennial
