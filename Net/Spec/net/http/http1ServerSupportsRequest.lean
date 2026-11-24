/-
`http1ServerSupportsRequest(req)` (Go 1.27.3, `server.go`): whether the HTTP/1.x server takes the
request: version 1.x, or the `PRI * HTTP/2.0` upgrade preface; the request is only read (any fraction). Proved in `Net/Proof/net/http/http1ServerSupportsRequest.lean`.
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
abbrev http1ServerSupportsRequest.spec : Prop :=
  ∀ (req : Loc) (dq : DFrac) (r : net.http.Request),
  {{ (req ↦{dq} r : IProp GF) }}
    (App (Val (@! net.http.http1ServerSupportsRequest)) (Val #req))
  {{ RET #(decide (r.ProtoMajor' = W64 1) || decide (r.ProtoMajor' = W64 2 ∧ r.ProtoMinor' = W64 0 ∧
        r.Method' = go!"PRI" ∧ r.RequestURI' = go!"*")); req ↦{dq} r }}

end spec

end net.http
end Perennial
