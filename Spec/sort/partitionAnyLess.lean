/-
`sort.partition(data, a, b, pivot)` for a `Less` that answers anything (`sorterAnySpec`, `Spec/sort/SortAnyLess.lean`); one of the callees of `sort.Sort.anyLessSpec`'s proof. It returns the new pivot's index, in `[a, b)`.
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

abbrev sort.partition.anyLessSpec : Prop :=
  ∀ (E : Type) (x : GoInterfaceOk) (R : List E → IProp GF) (l : List E) (a b pivot : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.sort ∗ sorterAnySpec x R ∗ R l ∗
      ⌜0 ≤ sint.Z a ∧ sint.Z a < sint.Z b ∧ sint.Z b ≤ l.length ∧ l.length ≤ 2 ^ 62 ∧
        sint.Z a ≤ sint.Z pivot ∧ sint.Z pivot < sint.Z b⌝ }}
    (App (App (App (App (Val (@! sort.partition)) (Val #(GoInterface.ok x))) (Val #a)) (Val #b)) (Val #pivot))
  {{ (l' : List E) (bl : Bool) (r : w64), RET (PairV #r #bl);
      R l' ∗ ⌜l.Perm l' ∧ sint.Z a ≤ sint.Z r ∧ sint.Z r < sint.Z b⌝ }}

end spec

end EtcdGrove
end Perennial
