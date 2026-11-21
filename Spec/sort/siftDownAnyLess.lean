/-
`sort.siftDown(data, lo, hi, first)` for a `Less` that answers anything (`sorterAnySpec`, `Spec/sort/SortAnyLess.lean`); one of the callees of `sort.Sort.anyLessSpec`'s proof. The indices it passes are `first + root` and `first + child` with `child < hi`.
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

abbrev sort.siftDown.anyLessSpec : Prop :=
  ∀ (E : Type) (x : GoInterfaceOk) (R : List E → IProp GF) (l : List E) (lo hi first : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.sort ∗ sorterAnySpec x R ∗ R l ∗
      ⌜0 ≤ sint.Z lo ∧ sint.Z lo ≤ sint.Z hi ∧ sint.Z lo < 2 ^ 62 ∧ 0 ≤ sint.Z first ∧
        sint.Z first + sint.Z hi ≤ l.length ∧ l.length ≤ 2 ^ 62⌝ }}
    (App (App (App (App (Val (@! sort.siftDown)) (Val #(GoInterface.ok x))) (Val #lo)) (Val #hi)) (Val #first))
  {{ (l' : List E), RET #(); R l' ∗ ⌜l.Perm l'⌝ }}

end spec

end EtcdGrove
end Perennial
