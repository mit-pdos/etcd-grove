/-
`metav1.LabelSelectorAsSelector(ps)` (`k8s.io/apimachinery/pkg/apis/meta/v1/helpers.go:36`, names
only here): the `labels.Selector` of a `*LabelSelector`: `labels.Nothing()` for `nil`,
`labels.Everything()` for one with no pair and no expression, otherwise the requirements of its
`MatchLabels` pairs (`Equals`) and `MatchExpressions` (`In`, `NotIn`, `Exists`, `DoesNotExist`; any
other operator, or a requirement `labels.NewRequirement` rejects, is an error). The trust boundary:
an axiom, `Proof/k8s_io/apimachinery/pkg/apis/meta/v1/LabelSelectorAsSelector.lean`. Lean-first;
phase 4 of `notes/k8s-daemonset-plan.md`.
-/
module

public import Proof.k8s_io.apimachinery.pkg.apis.meta.v1.SelDefs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace labels

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **`LabelSelectorAsSelector(ls)`** on a selector holding `S` (`lsOwn`): an error exactly when it
rejects `S` (`selValid`), otherwise a selector with `S`'s semantics (`selOk`: `Empty()` is
`selEmpty S`, `Matches(L)` is `selMatch S L`). -/
abbrev LabelSelectorAsSelector.spec : Prop :=
  ∀ (ls : Loc) (S : Option SelV),
  {{ lsOwn (GF := GF) ls S }}
    (App (Val (@! k8s_io.apimachinery.pkg.apis.«meta».v1.LabelSelectorAsSelector)) (Val #ls))
  {{ (sel : k8s_io.apimachinery.pkg.labels.Selector) (err : GoInterface), RET (PairV #sel #err);
      ⌜err ≠ interface.nil ∧ ¬ selValid S⌝ ∨ (⌜err = interface.nil ∧ selValid S⌝ ∗ selOk sel S) }}

end spec

end labels
end EtcdGrove
end Perennial
