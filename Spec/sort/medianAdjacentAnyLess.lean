/-
`sort.medianAdjacent(data, a, swaps)` for a `Less` that answers anything (`sorterAnySpec`, `Spec/sort/SortAnyLess.lean`); one of the callees of `sort.Sort.anyLessSpec`'s proof. It returns an index in `[a-1, a+1]`.
-/
module

public import Spec.sort.SortAnyLess

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

abbrev sort.medianAdjacent.anyLessSpec : Prop :=
  ∀ (E : Type) (x : GoInterfaceOk) (R : List E → IProp GF) (l : List E) (a : w64)
    (swaps_l : Loc) (swaps : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.sort ∗ sorterAnySpec x R ∗ R l ∗ swaps_l ↦ swaps ∗
      ⌜1 ≤ sint.Z a ∧ sint.Z a < l.length - 1 ∧ l.length ≤ 2 ^ 62⌝ }}
    (App (App (App (Val (@! sort.medianAdjacent)) (Val #(GoInterface.ok x))) (Val #a)) (Val #swaps_l))
  {{ (r swaps' : w64), RET #r;
      R l ∗ swaps_l ↦ swaps' ∗ ⌜sint.Z a - 1 ≤ sint.Z r ∧ sint.Z r ≤ sint.Z a + 1⌝ }}

end spec

end EtcdGrove
end Perennial
