/-
`e.Error()` on a `*pbcodec.Error` `e` kept for good (`↦□`) (the error a generated protobuf codec returns): `"proto: "`
followed by its `Msg`. Proved in `Net/Proof/models_lab/pbcodec/Error__Error.lean`.
-/
module

public import Net.Proof.models_lab.pbcodec.Base

@[expose] public section

set_option linter.iris.dupNamespace false

noncomputable section

namespace Perennial

open Iris Iris.BI

namespace models_lab.pbcodec

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem' : models_lab.pbcodec.Assumptions]

/-- See the file header. -/
abbrev Error.Error.spec : Prop :=
  ∀ (e : Loc) (v : models_lab.pbcodec.Error),
  {{ (e ↦□ v : IProp GF) }}
    (App (Val #(methods (go.GoType.PointerType Error.ty) go!"Error" #e)) (Val #()))
  {{ RET #((go!"proto: " : GoString) ++ v.Msg'); True }}

end spec

end models_lab.pbcodec
end Perennial
