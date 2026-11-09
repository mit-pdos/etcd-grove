/-
`(*clientv3.Client).autoSync` (`client/v3/client.go`).

Users: `newClient` (a goroutine).

Proof sketch: no interval: returns. Else a loop: the client's context done: returns; after the
interval, `Sync` with a timeout child of `c.ctx` (`ctxPrin_child`; `verifyOff`: `cfgOk`'s, kept in
`clientCore`), its error logged.

Changes: from `specs-ref/Spec/go_etcd_io/etcd/client/v3/Client__autoSync.lean` (the interval `0`
only): any interval.

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

/-- `c.autoSync()`: syncs the endpoints until the client is closed. -/
def Client.autoSync.spec : Prop :=
  ∀ (c : Loc) (γ : Cluster) (who : Principal),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ clientCore c γ who }}
    (App (Val (c @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.Client.ty @!! go!"autoSync")) (Val #()))
  {{ RET #(); True }}

end spec

end ClientV3
end EtcdGrove
end Perennial
