/-
`r.wantsHttp10KeepAlive()` (`request.go`) on a request whose header has no `Connection` entry:
`false` (an HTTP/1.0 request then asks for no keep-alive); the request and its header map only
read (any fractions). Proved in `Net/Proof/net/http/Request__wantsHttp10KeepAlive.lean`.
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
abbrev Request.wantsHttp10KeepAlive.spec : Prop :=
  ∀ (req : Loc) (dq dqm : DFrac) (r : net.http.Request) (ms : GMap GoString GoSlice),
  {{ (req ↦{dq} r ∗ r.Header' ↦${dqm} ms ∗ ⌜ms !! go!"Connection" = none⌝ : IProp GF) }}
    (App (Val #(methods (go.GoType.PointerType net.http.Request.ty) go!"wantsHttp10KeepAlive" #req))
      (Val #()))
  {{ RET #false; req ↦{dq} r ∗ r.Header' ↦${dqm} ms }}

end spec

end net.http
end Perennial
