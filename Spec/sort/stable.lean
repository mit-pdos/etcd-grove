/-
`sort.stable` over a `sort.Interface` (the sorter of `Spec/sort/Sort.lean`): the sorter ends
holding `stableM` of its list (`Proof/sort/StableModel.lean`), the code's own steps; what that
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

/-- `stable(data, n)`, for `n` the sorter's length. -/
abbrev sort.stable.spec : Prop :=
  ∀ (E : Type) (x : GoInterfaceOk) (R : List E → IProp GF) (lt : E → E → Bool) (l : List E)
    (n : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.sort ∗ sorterSpec x R lt ∗ R l ∗
      ⌜sint.Z n = l.length ∧ l.length ≤ 2 ^ 62⌝ }}
    (App (App (Val (@! sort.stable)) (Val #(GoInterface.ok x))) (Val #n))
  {{ RET #(); R (stableModel.stableM lt l l.length) }}

end spec

end EtcdGrove
end Perennial
