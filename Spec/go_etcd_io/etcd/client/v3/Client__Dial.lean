/-
`(*clientv3.Client).Dial` (`client/v3/client.go`).

Users: `NewMaintenance`'s dial closure (`Status`, `HashKV`, `Defragment`, `Snapshot` of one member).

Proof sketch: `credentialsForEndpoint(ep)`, `resolver.New(ep)` (`dialTargetOk` from `servesAt γ ep`),
`dial`.

Changes: new (no old spec).

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

/-- `c.Dial(ep)`: a connection to the member at `ep`, or an error. -/
def Client.Dial.spec : Prop :=
  ∀ (c : Loc) (γ : Cluster) (who : Principal) (ep : GoString) (dq : DFrac) (eps : List GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ clientPre c γ who ∗ servesAt γ ep ∗ epsTok c dq eps ∗ ⌜eps ≠ []⌝ }}
    (App (Val (c @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.Client.ty @!! go!"Dial")) (Val #ep))
  {{ (conn : Loc) (err : GoInterface), RET (PairV #conn #err); epsTok c dq eps ∗
      ((⌜err = GoInterface.nil⌝ ∗ connOk conn γ who) ∨ ⌜conn = null ∧ err ≠ GoInterface.nil⌝) }}

end spec

end ClientV3
end EtcdGrove
end Perennial
