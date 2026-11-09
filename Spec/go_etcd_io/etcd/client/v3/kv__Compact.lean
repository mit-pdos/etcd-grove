/-
`(*clientv3.kv).Compact` (`client/v3/kv.go`).

Users: the cache (`cache/demux.go`, through the client it is given), leasing (`leasing/kv.go:120`),
Kubernetes' compactor (`etcd3/compact.go:269` `client.Compact(ctx, rev)` after winning the
compare-and-swap of `compact_rev_key`), the examples (`examples/etcd/compacted`,
`compactwatch/compactkv.go`). Snippet: `clientv3kv/history.go` (`ReqCompactReached`).

Proof sketch: `OpCompact.spec` folds the options (`compactOptsAt`, given back), `CompactOp.toRequest.spec`
allocates the request (`compactReqOwn`), then the remote's `Compact` (`kvHandle`'s
`remoteKVAt`, `RemoteKV.CompactTriple` with the client's call options, not repeatable), the
caller's update passed through; `ContextError.spec` maps the error (`.etcd e` to `errVal e`).

Changes: from `specs-ref/Spec/go_etcd_io/etcd/client/v3/kv__Compact.lean`: the old premise "the KV
has reached `rev`" (`kvRevLb`) is gone: `rev` above the current revision is `ErrFutureRev`, a
linearized answer; the scope restriction `rev ≠ 0` stays (was `1 ≤ rev`; a negative `rev` is
`ErrCompacted`, as mvcc says).

verify-round: the request carries the caller's `rev` by `compactOptAt_rev` (the options keep the
revision; A1-provability F7).

Margin: `physical` makes the server wait for the compaction to reach the backend; the model
does not distinguish (the compaction revision is set when the request is applied).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.Api

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

/-- `kv.Compact` meets the KV contract's `Compact` (`KV.CompactTriple`, `Api.lean`), for a `*kv` of the
cluster `γ` as `who` (`kvHandle`). -/
def kv.Compact.spec : Prop :=
  ∀ (kv c : Loc) (γ : Cluster) (who : Principal),
  KV.CompactTriple (kv @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.kv.ty @!! go!"Compact")
    (iprop(isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ kvHandle kv c γ who ∗ clientReady c)) γ who

end spec

end ClientV3
end EtcdGrove
end Perennial
