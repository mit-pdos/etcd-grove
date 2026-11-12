/-
`(*clientv3.kv).GetStream` (`client/v3/kv.go`).

Users: Kubernetes' store (`etcd3/store.go:951` `GetList`'s streamed list, `KV.GetStream(ctx,
startKey, streamOpts...)`, then its own loop over the channel) and watcher (`etcd3/watcher.go:391`,
the initial list of a watch). Snippet: `clientv3kv/stream.go` (`ReqGetStream`).

Proof sketch: `OpGet.spec`; `kvHandle`'s remote: `RemoteKV.RangeStreamTriple` with the persistent update
(`toRangeRequest.spec`, the client's options); on an error, `ContextError.spec` (indefinite); else
a channel of capacity 1 (Perennial's `isSpsc`, the producer side to the goroutine, forked by
`wp_fork`: no thread token), whose loop receives from the wire stream (`wireStreamAt_recv`): a chunk
is sent with its message (`streamAt`'s per-chunk resource), `io.EOF` (`errors.Is(err, io.EOF)`: true
at the clean end, where `err` is `io.EOF`'s value; false for the error branches' errors, which are
not, by `errorsIs_callErr_eof`) closes the channel with the caller's `Q` (the spsc's final
resource), another error is sent as
the terminal chunk (`ContextError.spec`: `.etcd e` as `errVal e` with its `Q`; `ErrCompacted`
without `Q` when the server's pinned revision was compacted before a later read, before any chunk
too; else indefinite) and the channel closed. An open error (the stream interceptor
re-authenticates at every open) is a refusal that fired nothing or indefinite. The revision asked
is not negative (premise: such a stream is not pinned).

Changes: none (no old spec): Kubernetes' store now lists with it.
verify-round: no thread token (A1-completeness F1: it was taken and never given back on success,
so a request goroutine could not list; the goroutine needs none, `wp_fork`); the `io.EOF` test
closes by `wireStreamAt_recv`'s non-EOF errors and `errorsIs_callErr_eof` (A1-provability F3); the
scope premise `emptyEnd = false` (A1-provability F5).

Margin: a sorted or filtered stream's key-values are not modelled (`streamMatches`); a stream at the default ordering is the range's answer. If the consumer stops receiving, the goroutine blocks for good, a leaked goroutine (`nonissues/etcd-client-getstream-abandoned-leak.md`).
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

/-- `kv.GetStream` meets the KV contract's `GetStream` (`KV.GetStreamTriple`). -/
def kv.GetStream.spec : Prop :=
  ∀ (kv c : Loc) (γ : Cluster) (who : Principal),
  KV.GetStreamTriple (kv @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.kv.ty @!! go!"GetStream")
    (iprop(isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ kvHandle kv c γ who ∗ clientReady c)) γ who

end spec

end ClientV3
end EtcdGrove
end Perennial
