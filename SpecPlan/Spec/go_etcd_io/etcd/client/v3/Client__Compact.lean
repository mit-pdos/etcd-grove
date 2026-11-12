/-
`(*clientv3.Client).Compact`: the `KV` method promoted through `Client`'s embedded `KV` field.

Users: the cache (`cache/demux.go`, through the client it is given), leasing (`leasing/kv.go:120`),
Kubernetes' compactor (`etcd3/compact.go:269` `client.Compact(ctx, rev)` after winning the
compare-and-swap of `compact_rev_key`), the examples (`examples/etcd/compacted`,
`compactwatch/compactkv.go`). Snippet: `clientv3kv/history.go` (`ReqCompactReached`).

Proof sketch: `isClient_KV`: the field `c.KV` holds `v` with `kvAt v γ who`, read-only; the promoted
method loads it and calls `v.Compact` (Go's method set of `*Client`); `kvAt_methods`' `Compact` at `v`.

Changes: none (no old spec): the users call the KV methods on the client; added so that their proofs need no dispatch lemma.

Margin: as the KV method.
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.client.v3.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace ClientV3

open Iris Iris.BI EtcdModel EtcdWire
open Classical

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- `c.Compact(...)` on a client (`isClient`): the method of its `KV` field, promoted (`Client` embeds
`KV`): the KV contract's `Compact` (`KV.CompactTriple`). -/
def Client.Compact.spec : Prop :=
  ∀ (c : Loc) (γ : Cluster) (who : Principal),
  KV.CompactTriple (c @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.Client.ty @!! go!"Compact")
    (iprop(isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ isClient c γ who)) γ who

end spec

end ClientV3
end EtcdGrove
end Perennial
