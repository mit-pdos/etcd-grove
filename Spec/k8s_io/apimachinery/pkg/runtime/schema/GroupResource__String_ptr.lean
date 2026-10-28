/-
`(*schema.GroupResource).String`: the trust boundary (apimachinery's `runtime/schema` is translated
types and names only). Goose calls the value method `gr.String()` on the addressable loop variable
`gr` through the pointer's method set (`consistency.go:203`, the consistency store's error message).
Go's `GroupResource.String` returns `Resource`, or `Resource + "." + Group`; the spec says only
that it returns some string and leaves the variable unchanged. Lean-first.
-/
module

public import GeneratedProof.k8s_io.apimachinery.pkg.runtime.schema

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.apimachinery.pkg.runtime.schema.Assumptions]

/-- `(&gr).String()` of a group resource variable `l ↦{dq} gr`: some string; the variable is
unchanged. -/
abbrev schema.GroupResource.String_ptr.spec : Prop :=
  ∀ (l : Loc) (dq : DFrac) (gr : k8s_io.apimachinery.pkg.runtime.schema.GroupResource),
  {{ (l ↦{dq} gr : IProp GF) }}
    (App (Val (l @!! go.GoType.PointerType
      k8s_io.apimachinery.pkg.runtime.schema.GroupResource.ty @!! go!"String")) (Val #()))
  {{ (s : GoString), RET #s; l ↦{dq} gr }}

end spec

end EtcdGrove
end Perennial
