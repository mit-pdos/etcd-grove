/-
`kubernetes.Client.OptimisticPut` (`client/v3/kubernetes/client.go`).

Users: Kubernetes' etcd3 store (`Create`, `GuaranteedUpdate`: a compare-and-swap on the mod revision; `0` creates); W0's snippet `clientv3kv/txn.go` (`ReqCASModRevision`), `clientv3client/kubernetes.go` (`ReqKubeCAS`); through the `Interface` (`kubeAt`).

Proof sketch: `k.KV.Txn(ctx)` (W0's `KV.TxnTriple`), `If(Compare(ModRevision(key), "=", rev))`, `Then(OpPut(key, string(value), WithLease(lease)))`, `Else(OpGet(key))` if asked (W0's `Txn.*Triple`), `Commit()` with the caller's exclusive update; on failure with the get asked, the failure branch's one range response (`TxnRun`: one operation, one response) through `kvFromTxnResponse`; the `len(Responses) == 0` error is unreachable then.

Changes: from `specs-ref/Spec/go_etcd_io/etcd/client/v3/kubernetes/Client__OptimisticPut.lean` (over the old
client's members, `opts.LeaseID = 0`, key and value size bounds, a KV-only state): over W0's model,
any lease, no size premise, any principal.

Margin: none.
-/
module

public import Spec.go_etcd_io.etcd.client.v3.kubernetes.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Kubernetes

open Iris Iris.BI EtcdModel EtcdWire ClientV3
open Classical

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.kubernetes.Assumptions]

/-- `k.OptimisticPut(...)` of a client whose `clientv3.Client` is frozen: the store's request linearized by
the caller's update, or an error that settles nothing. -/
def Client.OptimisticPut.spec : Prop :=
  ∀ (k : go_etcd_io.etcd.client.v3.kubernetes.Client) (γ : Cluster) (who : Principal),
  Kube.OptimisticPutTriple (fun s => k @!! go_etcd_io.etcd.client.v3.kubernetes.Client.ty @!! s)
    iprop(isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.kubernetes ∗ isClient k.Client' γ who) γ who

end spec

end Kubernetes
end EtcdGrove
end Perennial
