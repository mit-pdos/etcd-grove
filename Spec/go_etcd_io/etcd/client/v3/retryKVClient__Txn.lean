/-
`(*clientv3.retryKVClient).Txn` (`client/v3/retry.go`).

Users: `kv.Do`, `kv.Compact`, `txn.Commit` (through `kvHandle`'s `remoteKVAt`).

Proof sketch: the stub's `Txn` with the same options (`retryKVHandle`'s `remoteKVAt`): the retry interceptor's default policy, not repeatable, resends only a request never sent (`isSafeRetryMutableRPC`), so the exclusive update passes.

Changes: from `specs-ref/Spec/go_etcd_io/etcd/client/v3/retryKVClient__Txn.lean`: restated over this branch's vocabulary (the `OpM` model, `opAt`, `optsAt`); otherwise unchanged.

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

/-- `rkv.Txn` meets the wire-level contract's `Txn` (`RemoteKV.TxnTriple`). -/
def retryKVClient.Txn.spec : Prop :=
  ∀ (rkv : Loc) (γ : Cluster) (who : Principal),
  RemoteKV.TxnTriple (rkv @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.retryKVClient.ty @!! go!"Txn")
    (iprop(isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ retryKVHandle rkv γ who)) γ who

end spec

end ClientV3
end EtcdGrove
end Perennial
