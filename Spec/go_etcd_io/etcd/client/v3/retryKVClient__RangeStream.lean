/-
`(*clientv3.retryKVClient).RangeStream` (`client/v3/retry.go`).

Users: `kv.GetStream`.

Proof sketch: the stub's `RangeStream` with the same options (a stream is not retried by the unary interceptor; the stream interceptor, 1c, may reopen it before the first message: the update is persistent).

Integration (I1): the stub opens the stream through 1c's `siOk_call` (over 2a's `streamerOk_call` with
`V3rpc.rangeStreamSpec`); `wireStreamAt` is realized by 2a's stream laws and `rsReq`/`rsChunk`.
The client's `lo` (`authLb γ lo`) is carried: `rangeStreamSpec`'s request clause holds
`authLb γ lo ∗ etcdAU γ who (.range r) true lo Q`. The member receives the request's wire view
(`Proto.norm c`), which models the same range under `endsOk` (3h's `holds_norm`), what `kv.GetStream`'s
`emptyEnd = false` gives.

Changes: none (no old spec): added for the users named above.
verify-round (second pass): the stale "Open" note on `lo` dropped (2a carries it; A6-completeness
C-F1).

Margin: none.
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

/-- `rkv.RangeStream` meets the wire-level contract's `RangeStream`. -/
def retryKVClient.RangeStream.spec : Prop :=
  ∀ (rkv c : Loc) (γ : Cluster) (who : Principal),
  RemoteKV.RangeStreamTriple (rkv @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.retryKVClient.ty @!! go!"RangeStream")
    (iprop(isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ retryKVHandle rkv c γ who ∗ clientReady c)) γ who

end spec

end ClientV3
end EtcdGrove
end Perennial
