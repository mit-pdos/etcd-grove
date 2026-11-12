/-
Proof of `Spec/go_etcd_io/etcd/client/v3/internal/resolver/EtcdManualResolver__SetEndpoints.lean`: a trust-boundary axiom (item 5, client construction). Lean-first (no
Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.internal.resolver.EtcdManualResolver__SetEndpoints

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **Trust boundary** (item 5): `SetEndpoints(eps)` sets `r.endpoints = eps` and calls
`updateState`, which pushes the new state to the `ClientConn` only once the resolver is built
(`getCC(r)` is `nil` before: the manual resolver's `CC()` of a resolver not built, or its panic,
recovered). -/
axiom resolver.EtcdManualResolver.SetEndpoints.wp_proof : resolver.EtcdManualResolver.SetEndpoints.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
