/-
`sort.breakPatterns(data, a, b)` for a `Less` that answers anything (`sorterAnySpec`, `Spec/sort/SortAnyLess.lean`); one of the callees of `sort.Sort.anyLessSpec`'s proof.
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

abbrev sort.breakPatterns.anyLessSpec : Prop :=
  ∀ (E : Type) (x : GoInterfaceOk) (R : List E → IProp GF) (l : List E) (a b : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.sort ∗ sorterAnySpec x R ∗ R l ∗
      ⌜0 ≤ sint.Z a ∧ sint.Z a < sint.Z b ∧ sint.Z b ≤ l.length ∧ l.length ≤ 2 ^ 62⌝ }}
    (App (App (App (Val (@! sort.breakPatterns)) (Val #(GoInterface.ok x))) (Val #a)) (Val #b))
  {{ (l' : List E), RET #(); R l' ∗ ⌜l.Perm l'⌝ }}

end spec

end EtcdGrove
end Perennial
