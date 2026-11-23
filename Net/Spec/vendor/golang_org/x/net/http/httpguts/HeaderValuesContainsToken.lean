/-
`httpguts.HeaderValuesContainsToken(values, token)` (Go 1.27.3's vendored `golang.org/x/net`) on no
values: `false` (what net/http's `shouldClose` asks of a head without a `Connection` header).
Proved in `Net/Proof/vendor/golang_org/x/net/http/httpguts/HeaderValuesContainsToken.lean`.
-/
module

public import Net.Proof.net.http.Defs

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI

namespace vendor.golang_org.x.net.http.httpguts

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem' : vendor.golang_org.x.net.http.httpguts.Assumptions]

/-- See the file header. -/
abbrev HeaderValuesContainsToken.spec : Prop :=
  ∀ (values : GoSlice) (token : GoString),
  {{ (⌜values.len = W64 0⌝ : IProp GF) }}
    (App (App (Val (@! vendor.golang_org.x.net.http.httpguts.HeaderValuesContainsToken)) (Val #values))
      (Val #token))
  {{ RET #false; True }}

end spec

end vendor.golang_org.x.net.http.httpguts
end Perennial
