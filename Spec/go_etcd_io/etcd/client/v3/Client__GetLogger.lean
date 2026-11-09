/-
`(*clientv3.Client).GetLogger` (`client/v3/client.go`).

Users: `concurrency.NewSession`, the interceptors, `NewLeaseFromLeaseClient`, `NewMaintenance`,
the watcher (1b).

Proof sketch: an atomic load of `c.lg`, whose invariant (`clientPre`) holds an `isLogger` (every
store: `newClient`, `WithLogger`, stores one).

Changes: from `specs-ref/Spec/go_etcd_io/etcd/client/v3/Client__GetLogger.lean`: over `clientPre`.

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

/-- `c.GetLogger()`: a logger. -/
def Client.GetLogger.spec : Prop :=
  ∀ (c : Loc) (who : Principal),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ clientBase c who }}
    (App (Val (c @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.Client.ty @!! go!"GetLogger")) (Val #()))
  {{ (lg : Loc), RET #lg; Zap.isLogger lg }}

end spec

end ClientV3
end EtcdGrove
end Perennial
