/-
`(*ServeMux).HandleFunc`'s spec (`Net/Spec/net/http/ServeMux__HandleFunc.lean`), assumed: net/http's
`ServeMux.register` (the pattern's parse, the routing tree, the conflict check) is phase 7's S5
item 4, as for `Handle`. Lean-first.
-/
module

public import Net.Spec.net.http.ServeMux__HandleFunc

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

/-- **Trust-boundary axiom, interim**: `(*ServeMux).HandleFunc` meets its spec. Interim, retired by
phase 7's S5 (item 4: `ServeMux.register` proved, `MuxDefs` refined). -/
axiom ServeMux.HandleFunc.wp_proof : ServeMux.HandleFunc.spec (GF := GF) (hG := hG)

end proof

end net.http
end Perennial
