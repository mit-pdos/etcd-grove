/-
`e.Error()` on a `*jsoncodec.Error` `e` kept for good (`↦□`) (the error a generated JSON codec returns): `"json: "`
followed by its `Msg`. Proved in `Net/Proof/netmodels_lab/jsoncodec/Error__Error.lean`.
-/
module

public import Net.Proof.netmodels_lab.jsoncodec.Base

@[expose] public section

set_option linter.iris.dupNamespace false

noncomputable section

namespace Perennial

open Iris Iris.BI

namespace netmodels_lab.jsoncodec

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem' : netmodels_lab.jsoncodec.Assumptions]

/-- See the file header. -/
abbrev Error.Error.spec : Prop :=
  ∀ (e : Loc) (v : netmodels_lab.jsoncodec.Error),
  {{ (e ↦□ v : IProp GF) }}
    (App (Val #(methods (go.GoType.PointerType Error.ty) go!"Error" #e)) (Val #()))
  {{ RET #((go!"json: " : GoString) ++ v.Msg'); True }}

end spec

end netmodels_lab.jsoncodec
end Perennial
