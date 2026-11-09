/-
`(*clientv3.Client).SetEndpoints` (`client/v3/client.go`).

Users: `newClient`, `Sync`; (Kubernetes: none); snippet `clientv3client/lifecycle.go`.

Proof sketch: `epMu.Lock`; stores the caller's slice (kept: read-only); `c.resolver.SetEndpoints`
(`internal/resolver`'s spec: grpc's resolver state updated, 2a); `Unlock`.

Changes: from `specs-ref/Spec/go_etcd_io/etcd/client/v3/Client__SetEndpoints.lean`: endpoints of the
cluster (`servesAt`) instead of the old fixed address list.

Margin: none.
-/
module

public import Spec.go_etcd_io.etcd.client.v3.ApiLease

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

/-- `c.SetEndpoints(eps...)`: the client's endpoints replaced by `eps`, each serving `γ`. -/
def Client.SetEndpoints.spec : Prop :=
  ∀ (c : Loc) (γ : Cluster) (who : Principal) (sl : GoSlice) (eps : List GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ clientPre c γ who ∗ sl ↦*□ eps ∗ [∗list] ep ∈ eps, servesAt γ ep }}
    (App (Val (c @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.Client.ty @!! go!"SetEndpoints")) (Val #sl))
  {{ RET #(); True }}

end spec

end ClientV3
end EtcdGrove
end Perennial
