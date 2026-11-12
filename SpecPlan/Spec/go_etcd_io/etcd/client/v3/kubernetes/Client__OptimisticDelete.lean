/-
`kubernetes.Client.OptimisticDelete` (`client/v3/kubernetes/client.go`).

Users: Kubernetes' etcd3 store (`Delete`, `conditionalDelete`); snippet `clientv3client/kubernetes.go`; through the `Interface` (`kubeAt`).

Proof sketch: as `OptimisticPut`, with `OpDelete(key)`.

Changes: from `specs-ref/Spec/go_etcd_io/etcd/client/v3/kubernetes/Client__OptimisticDelete.lean` (over the old
client's members, `opts.LeaseID = 0`, key and value size bounds, a KV-only state): over W0's model,
any lease, no size premise, any principal.

Margin: none.
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.client.v3.kubernetes.Api

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

/-- `k.OptimisticDelete(...)` of a client whose `clientv3.Client` is frozen: the store's request linearized by
the caller's update, or an error that settles nothing. -/
def Client.OptimisticDelete.spec : Prop :=
  ∀ (k : go_etcd_io.etcd.client.v3.kubernetes.Client) (γ : Cluster) (who : Principal),
  Kube.OptimisticDeleteTriple (fun s => k @!! go_etcd_io.etcd.client.v3.kubernetes.Client.ty @!! s)
    iprop(isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.kubernetes ∗ isClient k.Client' γ who) γ who

end spec

end Kubernetes
end EtcdGrove
end Perennial
