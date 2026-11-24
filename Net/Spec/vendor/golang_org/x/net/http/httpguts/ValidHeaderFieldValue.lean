/-
`httpguts.ValidHeaderFieldValue(v)` (Go 1.27.3's vendored `golang.org/x/net`): whether no byte of `v`
is a control byte (below `0x20`, or `0x7f`) other than a tab (`isCTL`, `isLWS`). The model's
`modelReadMIMEHeader` runs it on a header line's value. Proved in
`Net/Proof/vendor/golang_org/x/net/http/httpguts/ValidHeaderFieldValue.lean`.
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
abbrev ValidHeaderFieldValue.spec : Prop :=
  ∀ (v : GoString),
  {{ (True : IProp GF) }}
    (App (Val (@! vendor.golang_org.x.net.http.httpguts.ValidHeaderFieldValue)) (Val #v))
  {{ RET #(v.all (fun c => decide (32 ≤ c.toNat ∧ c.toNat ≠ 127) || decide (c = W8 9))); True }}

end spec

end vendor.golang_org.x.net.http.httpguts
end Perennial
