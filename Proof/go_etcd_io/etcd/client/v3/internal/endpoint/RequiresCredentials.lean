/-
Proof of `Spec/go_etcd_io/etcd/client/v3/internal/endpoint/RequiresCredentials.lean`: a trust-boundary axiom (item 5, client construction). Lean-first (no
Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.internal.endpoint.RequiresCredentials

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

/-- **Trust boundary** (item 5): `RequiresCredentials(ep)` is `translateEndpoint(ep)`'s third
result (`endpoint.go`): `schemeToCredsRequirement` of a scheme (one of `CredsRequire` (0),
`CredsDrop` (1), `CredsOptional` (2)), or `CredsOptional` for an endpoint with no `://` that is
not a unix socket's (and on a URL parse error); it does not panic (`mustSplit2` is called only
where its separator is present). -/
axiom endpoint.RequiresCredentials.wp_proof : endpoint.RequiresCredentials.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
