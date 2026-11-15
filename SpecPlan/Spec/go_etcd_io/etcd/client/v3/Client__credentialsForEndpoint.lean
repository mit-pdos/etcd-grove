/-
`(*clientv3.Client).credentialsForEndpoint` (`client/v3/client.go`).

Users: `dialWithBalancer`, `Dial`.

Proof sketch: `endpoint.RequiresCredentials(ep)` (its spec: one of the three requirements, so the
`panic` default is unreachable); `nil`, `c.creds`, or `NewTransportCredential(nil)`.

Changes: from `specs-ref/Spec/go_etcd_io/etcd/client/v3/Client__credentialsForEndpoint.lean`.

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

/-- `c.credentialsForEndpoint(ep)`: transport credentials for `ep`. -/
def Client.credentialsForEndpoint.spec : Prop :=
  ∀ (c : Loc) (γ : Cluster) (who : Principal) (ep : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ clientPre c γ who }}
    (App (Val (c @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.Client.ty @!! go!"credentialsForEndpoint")) (Val #ep))
  {{ (creds : GoInterface), RET #creds; transportCredsOk creds }}

end spec

end ClientV3
end EtcdGrove
end Perennial
