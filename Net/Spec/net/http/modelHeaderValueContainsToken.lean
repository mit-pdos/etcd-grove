/-
`modelHeaderValueContainsToken(v, token)` (httpguts' `headerValueContainsToken`, `textproto_model.go`):
some answer, needing nothing (its value is not specified). Proved in
`Net/Proof/net/http/modelHeaderValueContainsToken.lean`.
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
abbrev modelHeaderValueContainsToken.spec : Prop :=
  ∀ (v token : GoString),
  {{ (True : IProp GF) }}
    (App (App (Val (@! net.http.modelHeaderValueContainsToken)) (Val #v)) (Val #token))
  {{ (b : Bool), RET #b; True }}

end spec

end net.http
end Perennial
