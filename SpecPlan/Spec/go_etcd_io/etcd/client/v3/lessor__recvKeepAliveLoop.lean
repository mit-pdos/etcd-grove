/-
`(*clientv3.lessor).recvKeepAliveLoop` (`client/v3/lease.go`).

Users: `KeepAlive` (a goroutine, started once).

Proof sketch: a loop: `resetRecv` (its spec: the receiving half, or an error); on an error, `l.lg.Warn` (the
handle's logger: `isLogger`, never `nil`), stops if `canceledByCaller(l.stopCtx, err)`; else receives
until an error (`kaRecvAt_recv`), handing each response to `recvKeepAlive`, on `ErrNoLeader` calling
`closeRequireLeader`; waits `retryConnWait` or the stop. The deferred cleanup, under `l.mu`: closes
`donec` (its close token: the `Once`'s, given to this goroutine), sets `loopErr`, closes every entry
(`keepAlive.close`), empties the map.

Changes: from `specs-ref/Spec/go_etcd_io/etcd/client/v3/lessor__recvKeepAliveLoop.lean`: restated over `lessorHandle`.

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

/-- `l.recvKeepAliveLoop()`: the receive loop: runs until the lessor is stopped, then closes every channel. -/
def lessor.recvKeepAliveLoop.spec : Prop :=
  ∀ (l c : Loc) (γ : Cluster) (who : Principal),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ lessorHandle l c γ who ∗ clientReady c }}
    (App (Val (l @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.lessor.ty @!! go!"recvKeepAliveLoop")) (Val #()))
  {{ (v : val), RET v; True }}

end spec

end ClientV3
end EtcdGrove
end Perennial
