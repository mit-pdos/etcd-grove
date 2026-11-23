/-
`http.ParseHTTPVersion(vers)` on `"HTTP/1.0"` or `"HTTP/1.1"` (the versions the switch at its top
answers; the general case calls `strconv.ParseUint`): `(1, 0, true)` or `(1, 1, true)`. What
`ReadResponse` meets on net/rpc's answer. Proved in `Net/Proof/net/http/ParseHTTPVersion.lean`.
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
abbrev ParseHTTPVersion.spec : Prop :=
  ∀ (vers : GoString),
  {{ (⌜vers = go!"HTTP/1.0" ∨ vers = go!"HTTP/1.1"⌝ : IProp GF) }}
    (App (Val (@! net.http.ParseHTTPVersion)) (Val #vers))
  {{ RET (PairV (PairV #(W64 1) #(if vers = go!"HTTP/1.0" then W64 0 else W64 1)) #true); True }}

end spec

end net.http
end Perennial
