/-
Proof of `Spec/go_etcd_io/etcd/client/v3/NewLease.lean`: a trust-boundary axiom (item 5, client construction). Lean-first (no
Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.NewLease

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- **Trust boundary** (item 5): `NewLease(c)` returns `NewLeaseFromLeaseClient(RetryLeaseClient(c), c, c.cfg.DialTimeout+time.Second)`: a `*lessor` with its
maps and channel, `c.GetLogger()`, `c.callOpts`, and a cancellable context over
`WithRequireLeader(context.Background())`; no goroutine (the keep-alive loop starts with the first
`KeepAlive`): allocations and reads of `c`'s
fields, which `New` set and never writes again; it returns. -/
axiom NewLease.wp_proof : NewLease.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
