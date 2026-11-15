/-
`(*clientv3.Client).dialWithBalancer` (`client/v3/client.go`).

Users: `newClient`.

Proof sketch: `credentialsForEndpoint(c.Endpoints()[0])` (`newClient` checked one endpoint exists:
`clientPre`'s endpoints are not empty), `grpc.WithResolvers(c.resolver)` (`dialTargetOk`: the
resolver's endpoints are the client's), `dial`.

Changes: from `specs-ref/Spec/go_etcd_io/etcd/client/v3/Client__dialWithBalancer.lean`: over
`clientPre`.

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

/-- `c.dialWithBalancer()`: the client's connection, or an error. -/
def Client.dialWithBalancer.spec : Prop :=
  ∀ (c : Loc) (γ : Cluster) (who : Principal) (dq : DFrac) (eps : List GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ clientPre c γ who ∗ epsTok c dq eps ∗ ⌜eps ≠ []⌝ }}
    (App (Val (c @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.Client.ty @!! go!"dialWithBalancer")) (Val #slice.nil))
  {{ (conn : Loc) (err : GoInterface), RET (PairV #conn #err); epsTok c dq eps ∗
      ((⌜err = GoInterface.nil⌝ ∗ connOk conn γ who) ∨ ⌜conn = null ∧ err ≠ GoInterface.nil⌝) }}

end spec

end ClientV3
end EtcdGrove
end Perennial
