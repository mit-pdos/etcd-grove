/-
`http.Serve`'s spec on an rpc listener (`Net/Spec/net/http/Serve.lean`, `Serve.spec_rpc`),
assumed: net/http's server (`Server.Serve`'s accept loop, `conn.serve`'s request head and dispatch
through `DefaultServeMux` to the handler, the hijack) is phase 7's S5. Lean-first.
-/
module

public import Net.Spec.net.http.Serve

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Net

namespace net.http

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem' : net.http.Assumptions] [field_sem : net.FieldAssumptions]
variable [π : NetProtoGS]

/-- **Trust-boundary axiom, interim**: `http.Serve` meets `Serve.spec_rpc`. Interim, retired by
phase 7's S5 (net/http's server proved; its one `Serve.spec` implies this one). -/
axiom Serve.wp_proof_rpc : Serve.spec_rpc (GF := GF) (hG := hG)

end proof

end net.http
end Perennial
