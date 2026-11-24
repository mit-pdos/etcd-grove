/-
`httpguts.ValidHeaderFieldName(v)` (Go 1.27.3's vendored `golang.org/x/net`): whether `v` is RFC 7230's
`token`, not empty and every byte a `tchar` (`fieldByte`), read from the table `isTokenTable`
(`tokenTable`, `Net/Proof/vendor/golang_org/x/net/http/httpguts/Defs.lean`). net/http's `isToken`
(`validMethod`) runs it. Proved in
`Net/Proof/vendor/golang_org/x/net/http/httpguts/ValidHeaderFieldName.lean`.
-/
module

public import Net.Proof.vendor.golang_org.x.net.http.httpguts.Defs

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
abbrev ValidHeaderFieldName.spec : Prop :=
  ∀ (v : GoString),
  {{ (tokenTable : IProp GF) }}
    (App (Val (@! vendor.golang_org.x.net.http.httpguts.ValidHeaderFieldName)) (Val #v))
  {{ RET #(!v.isEmpty && v.all net.http.fieldByte); True }}

end spec

end vendor.golang_org.x.net.http.httpguts
end Perennial
