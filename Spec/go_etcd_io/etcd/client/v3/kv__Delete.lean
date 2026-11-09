/-
`(*clientv3.kv).Delete` (`client/v3/kv.go`).

Users: `client/v3/concurrency` (`mutex.go:118` `Unlock`'s `Delete` of the key, `election.go:124`
`Resign` via `Txn`), `experimental/recipes` (`double_barrier.go`, `rwmutex.go` `Unlock`),
leasing (`leasing/kv.go` `Delete` through `Do`), the examples (`txnlin/linkvtxn.go:885`
`callDel`). Snippets: `clientv3kv/put_get.go` (`ReqDeleteThenGet`).

Proof sketch: `OpDelete.spec` (premises `¬ prefixAndFromKey gs`, `¬ deletePanics`), then `kv.Do.spec`
with `.deleteRange (opDeleteM key gs).deleteReq` (exclusive update); `ContextError.spec`.

Changes: from `specs-ref/Spec/go_etcd_io/etcd/client/v3/kv__Delete.lean`: as `kv.Put`'s.

Margin: as `kv.Put`.
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

/-- `kv.Delete` meets the KV contract's `Delete` (`KV.DeleteTriple`, `Api.lean`), for a `*kv` of the
cluster `γ` as `who` (`kvHandle`). -/
def kv.Delete.spec : Prop :=
  ∀ (kv : Loc) (γ : Cluster) (who : Principal),
  KV.DeleteTriple (kv @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.kv.ty @!! go!"Delete")
    (iprop(isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ kvHandle kv γ who)) γ who

end spec

end ClientV3
end EtcdGrove
end Perennial
