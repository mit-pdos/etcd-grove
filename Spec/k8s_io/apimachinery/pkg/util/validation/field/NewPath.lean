/-
`field.NewPath(name, moreNames...)` (apimachinery, names only): **the trust boundary**. Lean-first
(no Rocq counterpart).
-/
module

public import GeneratedProof.k8s_io.apimachinery.pkg.util.validation.field

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace field

open Iris Iris.BI 

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- See the file header. -/
abbrev NewPath.spec : Prop :=
  ∀ (name : GoString) (s : GoSlice) (dq : DFrac) (more : List GoString),
  {{ (s ↦*{dq} more : IProp GF) }}
    (App (App (Val (@! _root_.Perennial.k8s_io.apimachinery.pkg.util.validation.field.NewPath))
      (Val #name)) (Val #s))
  {{ (p : Loc), RET #p; s ↦*{dq} more }}

end spec

end field
end EtcdGrove
end Perennial
