/-
`(*clientv3.kv).Do` (`client/v3/kv.go`).

Users: leasing (`leasing/kv.go:244` `Do` of every operation it forwards, `leasing/cache.go`), the
cache (`cache/cache.go`, `cache/watcher.go` `Do(OpGet(...))`), Kubernetes' compactor
(`etcd3/compact.go`). Snippet: `clientv3kv/ops.go` (`ReqDo`).

Proof sketch: `kvHandle`: `kv.remote` is a `remoteKVAt` value, `kv.callOpts` the client's (`callOptsOk _
false`). By `op.t` (`opAt_unfold`): a range: `IsSortOptionValid.spec`; if invalid, the code
returns `rpctypes.ErrInvalidSortOption` (`errVal .invalidSortOption`, rpctypes' init law, 2a),
and the proof **fires the caller's update itself** with `Step`'s answer `.err .invalidSortOption`
(the model's range step allows it for an invalid sort), giving `Q`; else `toRangeRequest.spec`
then `RemoteKV.RangeTriple` with the persistent update. A put or a delete: the request built in
place (`putReqOwn_unfold`, `deleteReqOwn_unfold` from the fresh struct's fields and the `Op`'s
read-only slices), `RemoteKV.PutTriple`/`DeleteRangeTriple`. A transaction: `toTxnRequest.spec`,
`RemoteKV.TxnTriple` with `□?(isRead)` as given. The wire reply (`wireReply`) is the
client-level one but for the error, which `ContextError.spec` maps (`.etcd e` to `errVal e`); the
indefinite case stays indefinite (`indefCall`). The zero `OpResponse{}` on error.

Changes: from `specs-ref/Spec/go_etcd_io/etcd/client/v3/kv__Do.lean`: every kind of `Op`, nested
transactions included (the old one covered a range, a put and a delete without lease); the
invalid-sort path is a linearized refusal.

verify-round: premise `o.emptyEnd = false` (A1-provability F5: under it `Wire.endOf` of the `Op`'s
`end` is `endReq`, and a member reached over gRPC reads the same range); a transaction's compares
(read-only, from `cmpAt`) and its fresh `RequestOp`s and `TxnRequest` are put at one `discard`
fraction by `protoRest_persist` (A1-provability F6).

Margin: as the methods above.
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

/-- `kv.Do` meets the KV contract's `Do` (`KV.DoTriple`, `Api.lean`), for a `*kv` of the
cluster `γ` as `who` (`kvHandle`). -/
def kv.Do.spec : Prop :=
  ∀ (kv c : Loc) (γ : Cluster) (who : Principal),
  KV.DoTriple (kv @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.kv.ty @!! go!"Do")
    (iprop(isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ kvHandle kv c γ who ∗ clientReady c)) γ who

end spec

end ClientV3
end EtcdGrove
end Perennial
