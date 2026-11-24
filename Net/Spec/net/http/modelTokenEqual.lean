/-
`modelTokenEqual(t1, t2)` (httpguts' `tokenEqual`, `textproto_model.go`): some answer, needing nothing
(what `modelHeaderValueContainsToken` asks: its value is not specified). Proved in
`Net/Proof/net/http/modelTokenEqual.lean`.
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
abbrev modelTokenEqual.spec : Prop :=
  ∀ (t1 t2 : GoString),
  {{ (True : IProp GF) }}
    (App (App (Val (@! net.http.modelTokenEqual)) (Val #t1)) (Val #t2))
  {{ (b : Bool), RET #b; True }}

end spec

end net.http
end Perennial
