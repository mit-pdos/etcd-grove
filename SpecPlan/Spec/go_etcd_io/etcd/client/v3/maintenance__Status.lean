/-
`(*clientv3.maintenance).Status` (`client/v3/maintenance.go`).

Users: Kubernetes' feature checker (`feature_support_checker.go`: the member's `Version`) and storage
prober (`etcd3.go`: `DbSize`), both through the promoted `Client.Status`; `Client.checkVersion`
(`RejectOldCluster`); snippet `clientv3client/maint.go` (`ReqStatus`).

Proof sketch: `m.dial(endpoint)` (the closure `NewMaintenance` built: `c.Dial(endpoint)` over the
endpoints token's fraction at a non-empty list (`Client.Dial.spec`; `maintOf v c`), or, for a
maintenance over a caller's remote, that remote), deferred `cancel` (closes the connection);
`remote.Status(ctx, &pb.StatusRequest{}, m.callOpts...)` (the stub: a fresh reply or a classified
error, 2a); `ContextError` on an error.

Changes: new (no old spec). Round 1: the endpoints token (`Client.dial` reads `c.endpoints[0]`
unlocked and unchecked: `issues/etcd-client-dial-empty-endpoints.md`).

Margin: the reply's fields are not related to the model (a member's local view).
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.client.v3.ApiClient

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

/-- `mt.Status(ctx, ep)`: the member's status reply (owned), or an error. -/
def maintenance.Status.spec : Prop :=
  ∀ (mt c : Loc) (γ : Cluster) (who : Principal),
  Maint.StatusTriple (fun s => mt @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.maintenance.ty @!! s)
    (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.client.v3.maintenance.ty) #mt) iprop(isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ maintHandle mt c γ who ∗ clientReady c) γ who

end spec

end ClientV3
end EtcdGrove
end Perennial
