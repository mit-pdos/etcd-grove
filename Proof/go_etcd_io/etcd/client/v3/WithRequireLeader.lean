/-
Proof of `Spec/go_etcd_io/etcd/client/v3/WithRequireLeader.lean`: a trust-boundary axiom (item 1, the
client lease; `WithRequireLeader` is names only: it needs grpc's `metadata`, which `client/v3`'s
translation does not import). Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.WithRequireLeader

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
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- **Trust boundary** (item 1, the client lease): `WithRequireLeader(Background())` is
`metadata.NewOutgoingContext(Background(), md)`, a `valueCtx` over `Background()`: never done, so
`WithCancel` of it propagates nothing (see the spec). -/
axiom WithRequireLeader.wp_proof : WithRequireLeader.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
