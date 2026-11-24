/-
`modelLowerASCII(b)` (httpguts' `lowerASCII`, `textproto_model.go`): `b` in lower case if it is an
ASCII upper-case letter (`lowerASCII`). Proved in `Net/Proof/net/http/modelLowerASCII.lean`.
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
abbrev modelLowerASCII.spec : Prop :=
  ∀ (b : w8),
  {{ (True : IProp GF) }}
    (App (Val (@! net.http.modelLowerASCII)) (Val #b))
  {{ RET #(lowerASCII b); True }}

end spec

end net.http
end Perennial
