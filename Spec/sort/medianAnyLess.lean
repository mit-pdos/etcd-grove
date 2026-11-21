/-
`sort.median(data, a, b, c, swaps)` for a `Less` that answers anything (`sorterAnySpec`, `Spec/sort/SortAnyLess.lean`); one of the callees of `sort.Sort.anyLessSpec`'s proof. It returns one of `a`, `b`, `c`.
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

abbrev sort.median.anyLessSpec : Prop :=
  ∀ (E : Type) (x : GoInterfaceOk) (R : List E → IProp GF) (l : List E) (a b c : w64)
    (swaps_l : Loc) (swaps : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.sort ∗ sorterAnySpec x R ∗ R l ∗ swaps_l ↦ swaps ∗
      ⌜0 ≤ sint.Z a ∧ sint.Z a < l.length ∧ 0 ≤ sint.Z b ∧ sint.Z b < l.length ∧
        0 ≤ sint.Z c ∧ sint.Z c < l.length⌝ }}
    (App (App (App (App (App (Val (@! sort.median)) (Val #(GoInterface.ok x))) (Val #a)) (Val #b)) (Val #c)) (Val #swaps_l))
  {{ (r swaps' : w64), RET #r; R l ∗ swaps_l ↦ swaps' ∗ ⌜r = a ∨ r = b ∨ r = c⌝ }}

end spec

end EtcdGrove
end Perennial
