/-
`clientv3.RetryMaintenanceClient` (`client/v3/retry.go`).

Users: `NewMaintenance` (over the client's connection, and over a member's own in its dial closure).

Proof sketch: the stub over `conn` (2a/3h), wrapped and persisted.

Changes: new (no old spec).

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

/-- `RetryMaintenanceClient(c, conn)`: a `*retryMaintenanceClient` over `conn`. -/
def RetryMaintenanceClient.spec : Prop :=
  ∀ (c conn : Loc) (γ : Cluster) (who : Principal),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ connOk conn γ who }}
    (App (App (Val (@! go_etcd_io.etcd.client.v3.RetryMaintenanceClient)) (Val #c)) (Val #conn))
  {{ (v : GoInterface), RET #v; ∃ r : Loc,
      ⌜v = interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.client.v3.retryMaintenanceClient.ty) #r⌝ ∗
      retryMaintHandle r c γ who }}

end spec

end ClientV3
end EtcdGrove
end Perennial
