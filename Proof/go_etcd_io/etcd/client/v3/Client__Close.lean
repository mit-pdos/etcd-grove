/-
**Trust boundary**: the client's `Close` returns (an axiom; see
`Spec/go_etcd_io/etcd/client/v3/Client__Close.lean`). Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.Client__Close

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

/-- **Trust boundary** (the auth plan's E2d): `Close` (`client.go`) cancels the client's context
(its own `cancel`), closes its `Watcher` (under the watcher's lock, each stream closed and the
streams map set to `nil`: `watcher.Close`, proved, keeps the watcher's invariant) and its `Lease`
(the lessor's `stopCancel`, then `donec` closed once through `firstKeepAliveOnce`, whose `Once`
owns that close, and waited for), and closes its gRPC connection (grpc's `ClientConn.Close`, after
which calls on it fail, as the attempt and stream axioms allow), returning `ContextError` of that or
the context's error. Every step keeps the invariants the proofs state of the client's objects; the
result is not specified. Not translated: `Close` reaches `lessor.Close` and grpc's `Close`, and
`ContextError` needs the client context's error facts (`ctxErrClient`), none of which `newClient`,
its one caller here, holds. -/
axiom Client.Close.wp_proof : Client.Close.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
