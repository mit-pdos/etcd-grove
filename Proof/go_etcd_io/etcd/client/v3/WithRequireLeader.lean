/-
Proof of `Spec/go_etcd_io/etcd/client/v3/WithRequireLeader.lean`: a trust-boundary axiom (item 1, the
client lease; k8s 7f-3a, T5-a; `WithRequireLeader` is names only: it needs grpc's `metadata`, which
`client/v3`'s translation does not import). Lean-first (no Rocq counterpart).
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

/-- **Trust boundary** (item 1, the client lease; k8s 7f-3a, T5-a: restated over a `watchCtx`
parent, decision D1, `notes/k8s-7f5-freeze.md` "T5-a addendum"): `WithRequireLeader(ctx)` is
`metadata.NewOutgoingContext(ctx, md)`, a `valueCtx` over `ctx` at grpc's `mdOutgoingKey{}`: every
other key, `Done`, `Err` and `Value(&cancelCtxKey)` (so `Cause`) are the parent's (Go evidence:
`examples/premisefix/watcherctx/requireleader_spec_test.go`). Over `Background()` it is never done, so
`WithCancel` of it propagates nothing (see the spec). Not translated: proved from a translation it
would need three or four trusted changes in place of this one (`notes/k8s-7f3a-draft.md` §6, D1). -/
axiom WithRequireLeader.wp_proof : WithRequireLeader.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
