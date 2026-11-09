/-
`(*clientv3.Client).roundRobinQuorumBackoff` (`client/v3/client.go`).

Users: `dialSetupOpts`.

Proof sketch: a closure: `len(c.Endpoints())/2 + 1` is at least `1` (no division by `0`),
`jitterUp` or `0`, the logger's `Debug`.

Changes: from `specs-ref/Spec/go_etcd_io/etcd/client/v3/Client__roundRobinQuorumBackoff.lean`.

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

/-- `c.roundRobinQuorumBackoff(w, j)`: a backoff function. -/
def Client.roundRobinQuorumBackoff.spec : Prop :=
  ∀ (c : Loc) (γ : Cluster) (who : Principal) (w j : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ clientPre c γ who }}
    (App (App (Val (c @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.Client.ty @!! go!"roundRobinQuorumBackoff")) (Val #w)) (Val #j))
  {{ (f : GoFunc), RET #f; backoffOk f }}

end spec

end ClientV3
end EtcdGrove
end Perennial
