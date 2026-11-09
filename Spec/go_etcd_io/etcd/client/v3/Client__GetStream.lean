/-
`(*clientv3.Client).GetStream` (`client/v3/kv.go`).

Users: Kubernetes' store (`etcd3/store.go:951` `GetList`'s streamed list, `KV.GetStream(ctx,
startKey, streamOpts...)`, then its own loop over the channel) and watcher (`etcd3/watcher.go:391`,
the initial list of a watch). Snippet: `clientv3kv/stream.go` (`ReqGetStream`).

Proof sketch: `isClient_KV`, `kvAt_methods`' `GetStream`.

Changes: none (no old spec): Kubernetes' store now lists with it.
verify-round: as `kv.GetStream`'s (no thread token; the scope premise `emptyEnd = false`).

Margin: a sorted or filtered stream's key-values are not modelled (`streamMatches`); a stream at the default ordering is the range's answer. If the consumer stops receiving, the goroutine blocks for good, a leaked goroutine (`nonissues/etcd-client-getstream-abandoned-leak.md`).
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

/-- `c.GetStream` meets the KV contract's `GetStream` (`KV.GetStreamTriple`). -/
def Client.GetStream.spec : Prop :=
  ∀ (c : Loc) (γ : Cluster) (who : Principal),
  KV.GetStreamTriple (c @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.Client.ty @!! go!"GetStream")
    (iprop(isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ isClient c γ who)) γ who

end spec

end ClientV3
end EtcdGrove
end Perennial
