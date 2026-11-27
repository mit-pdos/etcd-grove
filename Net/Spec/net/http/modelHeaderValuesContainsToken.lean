/-
`modelHeaderValuesContainsToken(values, token)` (the model's `httpguts.HeaderValuesContainsToken`,
`textproto_model.go`), `values` a slice of strings `vs`: some answer, `false` on no values (what
`shouldClose` asks of a head without a `Connection` header); the slice given back. Proved in
`Net/Proof/net/http/modelHeaderValuesContainsToken.lean`.
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
abbrev modelHeaderValuesContainsToken.spec : Prop :=
  ∀ (values : GoSlice) (vs : List GoString) (dq : DFrac) (token : GoString),
  {{ (values ↦*{dq} vs : IProp GF) }}
    (App (App (Val (@! net.http.modelHeaderValuesContainsToken)) (Val #values)) (Val #token))
  {{ (b : Bool), RET #b; values ↦*{dq} vs ∗ ⌜vs = [] → b = false⌝ }}

end spec

end net.http
end Perennial
