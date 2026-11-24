/-
`labels.Everything()` (`k8s.io/apimachinery/pkg/labels`, `selector.go`): it returns
`sharedEverythingSelector`, `internalSelector{}`, a selector that matches everything; the spec says it returns a non-nil
`Selector` whose `Empty()` is `true`, and which `labels.MatchesNothing` does not take for
`labels.Nothing()` (it compares with `sharedNothingSelector`, a `nothingSelector`: a different
dynamic type; 2026-10-27, for the listers' `List(labels.Everything())`). Proved over the code since
2026-11-21 (#25; until then a trust-boundary axiom): it reads the package's variables, so it takes
`labels`' initialization (fact `labelsInit`, `storage/etcd3/Base.lean`). Lean-first (no Rocq
counterpart).
-/
module

public import GeneratedProof.k8s_io.apimachinery.pkg.labels
public import Proof.k8s_io.apiserver.pkg.storage.etcd3.Base

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
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apimachinery.pkg.labels }}
    (App (Val (@! k8s_io.apimachinery.pkg.labels.Everything)) (Val #()))
  {{ (s : k8s_io.apimachinery.pkg.labels.Selector), RET #s; ∃ i : GoInterfaceOk, ⌜s = interface.ok i⌝ ∗
      {{ True }} (App (Val (@! _root_.Perennial.k8s_io.apimachinery.pkg.labels.MatchesNothing))
        (Val #s)) {{ RET #false; True }} ∗
      {{ True }} (App (Val #(methods i.ty go!"Empty" i.v)) (Val #())) {{ RET #true; True }} }}

end spec

end EtcdGrove
end Perennial
