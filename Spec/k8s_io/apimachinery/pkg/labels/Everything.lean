/-
`labels.Everything()` (`k8s.io/apimachinery/pkg/labels`, `selector.go`, names-only here): it returns
`internalSelector{}`, a selector that matches everything; the spec says it returns a non-nil
`Selector` whose `Empty()` is `true`, and which `labels.MatchesNothing` does not take for
`labels.Nothing()` (it compares with `sharedNothingSelector`, a `nothingSelector`: a different
dynamic type; 2026-10-27, for the listers' `List(labels.Everything())`). The trust boundary: an axiom, `Proof/k8s_io/apimachinery/pkg/labels/Everything.lean`. Lean-first (no Rocq
counterpart).
-/
module

public import GeneratedProof.k8s_io.apimachinery.pkg.labels

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- See the file header. -/
abbrev labels.Everything.spec : Prop :=
  {{ (True : IProp GF) }}
    (App (Val (@! k8s_io.apimachinery.pkg.labels.Everything)) (Val #()))
  {{ (s : k8s_io.apimachinery.pkg.labels.Selector), RET #s; ∃ i : GoInterfaceOk, ⌜s = interface.ok i⌝ ∗
      {{ True }} (App (Val (@! _root_.Perennial.k8s_io.apimachinery.pkg.labels.MatchesNothing))
        (Val #s)) {{ RET #false; True }} ∗
      {{ True }} (App (Val #(methods i.ty go!"Empty" i.v)) (Val #())) {{ RET #true; True }} }}

end spec

end EtcdGrove
end Perennial
