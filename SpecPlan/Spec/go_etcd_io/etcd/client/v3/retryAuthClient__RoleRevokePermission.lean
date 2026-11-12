/-
`(*clientv3.retryAuthClient).RoleRevokePermission` (`client/v3/retry.go`).

Users: `authClient.*` (through `remoteAuthAt`, `retryAuthHandle_remoteAuthAt`).

Proof sketch: passes the options through to the stub (non-repeatable: `callOptsOk _ false`): `rac.ac` is `pb.NewAuthClient(c.conn)`, the generated stub over the client's
connection (`retryAuthHandle`: the stub meets the wire contract over `connOk`, 2a/3h), whose triple is
`RemoteCallTriple` itself.

Changes: new (no old spec).

Margin: none.
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

/-- `r.RoleRevokePermission`: the wire contract at its request. -/
def retryAuthClient.RoleRevokePermission.spec : Prop :=
  ∀ (r c : Loc) (γ : Cluster) (who : Principal) (role key rangeEnd : GoString),
  RemoteCallTriple (fun s => r @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.retryAuthClient.ty @!! s)
    iprop(isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ retryAuthHandle r c γ who ∗ clientReady c) γ who (.roleRevokePermission role key rangeEnd)

end spec

end ClientV3
end EtcdGrove
end Perennial
