/-
`http.Handle`'s spec (`Net/Spec/net/http/Handle.lean`), assumed: net/http's `ServeMux.register`
(the pattern's parse, the routing tree, the conflict check, `runtime.Caller` for its message) is
phase 7's S5 item 4. Lean-first.
-/
module

public import Net.Spec.net.http.Handle

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

/-- **Trust-boundary axiom, interim**: `http.Handle` meets its spec. Interim, retired by phase 7's
S5 (item 4: `ServeMux.register` proved, `MuxDefs` refined). -/
axiom Handle.wp_proof : Handle.spec (GF := GF) (hG := hG)

end proof

end net.http
end Perennial
