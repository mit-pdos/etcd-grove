/-
`(*clientv3.kv).GetStream` (`client/v3/kv.go`).

Users: Kubernetes' store (`etcd3/store.go:951` `GetList`'s streamed list, `KV.GetStream(ctx,
startKey, streamOpts...)`, then its own loop over the channel) and watcher (`etcd3/watcher.go:391`,
the initial list of a watch). Snippet: `clientv3kv/stream.go` (`ReqGetStream`).

Proof sketch: `OpGet.spec`; `kvHandle`'s remote: `RemoteKV.RangeStreamTriple` with the persistent update
(`toRangeRequest.spec`, the client's options); on an error, `ContextError.spec` (indefinite); else
a channel of capacity 1 (Perennial's `isSpsc`, the producer side to the goroutine, with the
thread token: `wp_fork`), whose loop receives from the wire stream (`wireStreamAt_recv`): a chunk
is sent with its message (`streamAt`'s per-chunk resource), `io.EOF` (`errors.Is`, Perennial)
closes the channel with the caller's `Q` (the spsc's final resource), another error is sent as
the terminal chunk (`ContextError.spec`: `.etcd e` as `errVal e` with its `Q`, else indefinite)
and the channel closed.

Changes: none (no old spec): Kubernetes' store now lists with it.

Margin: a sorted or filtered stream's key-values are not modelled (`streamMatches`); a stream at the default ordering is the range's answer. The thread token comes back only for a drained stream: if the consumer stops receiving, the goroutine blocks for good (`nonissues/etcd-client-getstream-abandoned-leak.md`).
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

/-- `kv.GetStream` meets the KV contract's `GetStream` (`KV.GetStreamTriple`). -/
def kv.GetStream.spec : Prop :=
  ∀ (kv : Loc) (γ : Cluster) (who : Principal),
  KV.GetStreamTriple (kv @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.kv.ty @!! go!"GetStream")
    (iprop(isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ kvHandle kv γ who)) γ who

end spec

end ClientV3
end EtcdGrove
end Perennial
