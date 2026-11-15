/-
`(*clientv3.Client).Endpoints` (`client/v3/client.go`).

Users: Kubernetes' compactor (`compact.go`: the compactor's key per endpoint set, logging) and
feature checker (`Status` of each), `isSafeRetry` (the learner case), `dialWithBalancer`,
`roundRobinQuorumBackoff`, `checkVersion`; snippet `clientv3client/lifecycle.go` (`ReqEndpoints`).

Proof sketch: `epMu.RLock` (the client's `RWMutex`, its invariant holding `endpoints` and their
`servesAt`), a fresh copy, `RUnlock`.

Changes: from `specs-ref/Spec/go_etcd_io/etcd/client/v3/Client__Endpoints.lean`: over `clientPre`;
each endpoint serves the cluster.

Margin: none.
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.client.v3.ApiLease

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

/-- `c.Endpoints()`: a fresh copy of the endpoints, each serving `γ`. -/
def Client.Endpoints.spec : Prop :=
  ∀ (c : Loc) (γ : Cluster) (who : Principal),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ clientPre c γ who }}
    (App (Val (c @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.Client.ty @!! go!"Endpoints")) (Val #()))
  {{ (sl : GoSlice), RET #sl; ∃ eps : List GoString, sl ↦* eps ∗ [∗list] ep ∈ eps, servesAt γ ep }}

end spec

end ClientV3
end EtcdGrove
end Perennial
