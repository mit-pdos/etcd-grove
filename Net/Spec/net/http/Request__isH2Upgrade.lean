/-
`r.isH2Upgrade()` (`request.go`): whether the request is the `PRI * HTTP/2.0` preface with no
header; the request, its header map and its URL only read (any fractions). Proved in
`Net/Proof/net/http/Request__isH2Upgrade.lean`.
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
abbrev Request.isH2Upgrade.spec : Prop :=
  ∀ (req : Loc) (dq dqm dqu : DFrac) (r : net.http.Request) (ms : GMap GoString GoSlice)
    (u : net.url.URL),
  {{ (req ↦{dq} r ∗ r.Header' ↦${dqm} ms ∗ r.URL' ↦{dqu} u : IProp GF) }}
    (App (Val #(methods (go.GoType.PointerType net.http.Request.ty) go!"isH2Upgrade" #req))
      (Val #()))
  {{ RET #(decide (r.Method' = go!"PRI") && decide (GMap.size ms = 0) &&
        decide (u.Path' = go!"*") && decide (r.Proto' = go!"HTTP/2.0"));
      req ↦{dq} r ∗ r.Header' ↦${dqm} ms ∗ r.URL' ↦{dqu} u }}

end spec

end net.http
end Perennial
