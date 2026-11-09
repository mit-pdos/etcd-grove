/-
`(*clientv3.Client).ActiveConnection` (`client/v3/client.go`).

Users: Kubernetes' `blockUntilReady` (`storagebackend/factory/etcd3.go:358-380`: then `GetState`,
`Connect`, `WaitForStateChange` on the connection, which `connOk` gives no specs for: not served,
recorded as not done, `batch-1c.md` C-S1); the gRPC proxy, tests.

Proof sketch: reads `c.conn` (`clientCore`).

Changes: new (no old spec).
verify-round: the Users line (A2-completeness S2: it said no user).

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

/-- `c.ActiveConnection()`: the client's connection. -/
def Client.ActiveConnection.spec : Prop :=
  ∀ (c : Loc) (γ : Cluster) (who : Principal),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ clientCore c γ who }}
    (App (Val (c @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.Client.ty @!! go!"ActiveConnection")) (Val #()))
  {{ (conn : Loc), RET #conn; connOk conn γ who }}

end spec

end ClientV3
end EtcdGrove
end Perennial
