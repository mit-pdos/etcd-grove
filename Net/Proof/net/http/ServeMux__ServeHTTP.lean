/-
`(*ServeMux).ServeHTTP`'s spec (`Net/Spec/net/http/ServeMux__ServeHTTP.lean`), assumed: net/http's
mux dispatch (`findHandler`, the routing tree's match, the redirects, `NotFound`) is phase 7's S5
(`mux_handlerOk`). Lean-first.
-/
module

public import Net.Spec.net.http.ServeMux__ServeHTTP

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Net

namespace net.http

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem' : net.http.Assumptions]

/-- **Trust-boundary axiom, interim**: `(*ServeMux).ServeHTTP` meets its spec. Interim, retired by
phase 7's S5 (the mux's dispatch proved, `MuxDefs` refined). -/
axiom ServeMux.ServeHTTP.wp_proof : ServeMux.ServeHTTP.spec (GF := GF) (hG := hG)

end proof

end net.http
end Perennial
