/-
net/http's `isToken(v)` (`http.go`): httpguts' `ValidHeaderFieldName(v)`: whether `v` is RFC 7230's `token` (not empty, every byte a `fieldByte`), read from
httpguts' `isTokenTable` (`tokenTable`). Proved in `Net/Proof/net/http/isToken.lean`.
-/
module

public import Net.Proof.vendor.golang_org.x.net.http.httpguts.Defs

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
abbrev isToken.spec : Prop :=
  ∀ (v : GoString),
  {{ (vendor.golang_org.x.net.http.httpguts.tokenTable : IProp GF) }}
    (App (Val (@! net.http.isToken)) (Val #v))
  {{ RET #(!v.isEmpty && v.all fieldByte); True }}

end spec

end net.http
end Perennial
