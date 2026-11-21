/-
`sort.order2(data, a, b, swaps)` for a `Less` that answers anything (`sorterAnySpec`, `Spec/sort/SortAnyLess.lean`); one of the callees of `sort.Sort.anyLessSpec`'s proof. It returns `(a, b)` or `(b, a)`.
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

abbrev sort.order2.anyLessSpec : Prop :=
  ∀ (E : Type) (x : GoInterfaceOk) (R : List E → IProp GF) (l : List E) (a b : w64)
    (swaps_l : Loc) (swaps : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.sort ∗ sorterAnySpec x R ∗ R l ∗ swaps_l ↦ swaps ∗
      ⌜0 ≤ sint.Z a ∧ sint.Z a < l.length ∧ 0 ≤ sint.Z b ∧ sint.Z b < l.length⌝ }}
    (App (App (App (App (Val (@! sort.order2)) (Val #(GoInterface.ok x))) (Val #a)) (Val #b)) (Val #swaps_l))
  {{ (a' b' swaps' : w64), RET (PairV #a' #b');
      R l ∗ swaps_l ↦ swaps' ∗ ⌜(a' = a ∧ b' = b) ∨ (a' = b ∧ b' = a)⌝ }}

end spec

end EtcdGrove
end Perennial
