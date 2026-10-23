/-
`fields.Everything()` (`k8s.io/apimachinery/pkg/fields`, `selector.go`, names-only here): it
returns `andTerm{}`, a selector that matches everything; the spec says it returns some
`Selector`. The trust boundary: an axiom, `Proof/k8s_io/apimachinery/pkg/fields/Everything.lean`. Lean-first (no Rocq
counterpart).
-/
module

public import GeneratedProof.k8s_io.apimachinery.pkg.fields

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- See the file header. -/
abbrev fields.Everything.spec : Prop :=
  {{ (True : IProp GF) }}
    (App (Val (@! k8s_io.apimachinery.pkg.fields.Everything)) (Val #()))
  {{ (s : k8s_io.apimachinery.pkg.fields.Selector), RET #s; True }}

end spec

end EtcdGrove
end Perennial
