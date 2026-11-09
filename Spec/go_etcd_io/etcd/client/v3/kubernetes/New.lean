/-
`kubernetes.New` (`client/v3/kubernetes/client.go`).

Users: Kubernetes' storage factory (`storagebackend/factory/etcd3.go`: then wraps `client.KV` in a
latency tracker, `clientMut_KV`), its test server, `examples/k8s/*`; snippet
`clientv3client/kubernetes.go` (`ReqKubeNew`).

Proof sketch: `clientv3.New(cfg)` (its spec); a fresh `*Client` holding it, its `Kubernetes` field set
to itself.

Changes: from `specs-ref/Spec/go_etcd_io/etcd/client/v3/kubernetes/New.lean`: as `clientv3.New`'s.
verify-round: the endpoints token `clientv3.New` gives (auto-sync off) is passed on (A2-completeness
F1: without it no Kubernetes client could call `Status`, the feature checker's
`feature_support_checker.go:142,194`, or `Endpoints`). The snippet `ReqKubeStatus`
(`clientv3client/kubernetes.go`) covers the pattern.

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

/-- `New(cfg)`: a `*Client` whose `Kubernetes` field is itself, over a writable `clientv3.Client`
(the caller wraps its `KV`, then freezes it: `kubeClient_kubeAt`), or an error. -/
def New.spec : Prop :=
  ∀ (cfg : go_etcd_io.etcd.client.v3.Config) (γ : Cluster) (who : Principal),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.kubernetes ∗ cfgOk cfg γ who }}
    (App (Val (@! go_etcd_io.etcd.client.v3.kubernetes.New)) (Val #cfg))
  {{ (kc : Loc) (err : GoInterface), RET (PairV #kc #err);
      (⌜err = GoInterface.nil⌝ ∗ ∃ c : Loc,
        kc ↦ ({ Client' := c,
                 Kubernetes' := interface.mkOk
                   (go.GoType.PointerType go_etcd_io.etcd.client.v3.kubernetes.Client.ty) #kc } :
               go_etcd_io.etcd.client.v3.kubernetes.Client) ∗ clientMut c γ who ∗
        (∃ eps, cfg.Endpoints' ↦*□ eps ∗ epsTok c (DFrac.own 1) eps)) ∨
      ⌜kc = null ∧ err ≠ GoInterface.nil⌝ }}

end spec

end Kubernetes
end EtcdGrove
end Perennial
