/-
`fields.Everything()` (`k8s.io/apimachinery/pkg/fields`, `selector.go:76`): it
returns `andTerm{}` (a non-nil, length-0 value of the slice type `andTerm`); the spec says it
returns a non-nil `Selector` whose `Empty()` is `true` (`andTerm.Empty`, value receiver,
`selector.go:190`: `true` on `nil` or length 0, before its loop; pure, so the triple is
persistent), for `storage.Everything` (`storageInit`, 2026-11-16, k8s 7f-5b H2). Evidence:
`examples/premisefix/watcherctx/everything_test.go`. Proved over its translated body (2026-11-19; until then a trust-boundary axiom,
`Proof/k8s_io/apimachinery/pkg/fields/Everything.lean`). Lean-first (no Rocq counterpart).
-/
module

public import GeneratedProof.k8s_io.apimachinery.pkg.fields

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
abbrev fields.Everything.spec : Prop :=
  {{ (True : IProp GF) }}
    (App (Val (@! k8s_io.apimachinery.pkg.fields.Everything)) (Val #()))
  {{ (s : k8s_io.apimachinery.pkg.fields.Selector), RET #s; ∃ i : GoInterfaceOk, ⌜s = interface.ok i⌝ ∗
      {{ True }} (App (Val #(methods i.ty go!"Empty" i.v)) (Val #())) {{ RET #true; True }} }}

end spec

end EtcdGrove
end Perennial
