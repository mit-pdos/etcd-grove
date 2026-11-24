/-
`http.ParseHTTPVersion(vers)` on a prefix of `"HTTP/1.0"` or `"HTTP/1.1"` (a version a status or request
line holds, or what a line cut by an error leaves of it): `(1, 0, true)` and `(1, 1, true)` on the two
(the switch at its top), else `ok` false (a strict prefix fails `HasPrefix(vers, "HTTP/")` or the
length check, before the general case's `strconv.ParseUint`). What `ReadResponse` meets on net/rpc's and
net/http's `400` answers, and `readRequestLimit` on net/rpc's `CONNECT` request. `httpEnv`: `strings`'
initialization. Proved in `Net/Proof/net/http/ParseHTTPVersion.lean`.
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
  {{ (httpEnv ∗ ⌜vers <+: go!"HTTP/1.0" ∨ vers <+: go!"HTTP/1.1"⌝ : IProp GF) }}
    (App (Val (@! net.http.ParseHTTPVersion)) (Val #vers))
  {{ (major minor : w64) (ok : Bool), RET (PairV (PairV #major #minor) #ok);
      ⌜ok = decide (vers = go!"HTTP/1.0" ∨ vers = go!"HTTP/1.1") ∧
        (ok = true → major = W64 1 ∧ minor = (if vers = go!"HTTP/1.0" then W64 0 else W64 1))⌝ }}

end spec

end net.http
end Perennial
