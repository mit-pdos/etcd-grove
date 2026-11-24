/-
`modelTrimOWS(x)` (httpguts' `trimOWS`, `textproto_model.go`): `x` without the spaces and tabs at its
ends (`trimOWS`). Proved in `Net/Proof/net/http/modelTrimOWS.lean`.
-/
module

public import Net.Proof.net.http.Defs

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI

namespace net.http

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem' : net.http.Assumptions]

/-- See the file header. -/
abbrev modelTrimOWS.spec : Prop :=
  ∀ (x : GoString),
  {{ (True : IProp GF) }}
    (App (Val (@! net.http.modelTrimOWS)) (Val #x))
  {{ RET #(trimOWS x); True }}

end spec

end net.http
end Perennial
