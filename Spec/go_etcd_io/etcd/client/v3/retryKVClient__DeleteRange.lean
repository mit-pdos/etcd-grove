/-
`(*clientv3.retryKVClient).DeleteRange` (`client/v3/retry.go`).

Users: `kv.Do`, `kv.Compact`, `txn.Commit` (through `kvHandle`'s `remoteKVAt`).

Proof sketch: the stub's `DeleteRange` with the same options (`retryKVHandle`'s `remoteKVAt`): the retry interceptor's default policy, not repeatable, resends only a request never sent (`isSafeRetryMutableRPC`), so the exclusive update passes.

Changes: from `specs-ref/Spec/go_etcd_io/etcd/client/v3/retryKVClient__DeleteRange.lean`: restated over this branch's vocabulary (the `OpM` model, `opAt`, `optsAt`); otherwise unchanged.

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

/-- `rkv.DeleteRange` meets the wire-level contract's `DeleteRange` (`RemoteKV.DeleteRangeTriple`). -/
def retryKVClient.DeleteRange.spec : Prop :=
  ∀ (rkv : Loc) (γ : Cluster) (who : Principal),
  RemoteKV.DeleteRangeTriple (rkv @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.retryKVClient.ty @!! go!"DeleteRange")
    (iprop(isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ retryKVHandle rkv γ who)) γ who

end spec

end ClientV3
end EtcdGrove
end Perennial
