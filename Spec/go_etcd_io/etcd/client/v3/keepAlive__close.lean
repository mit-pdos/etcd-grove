/-
`(*clientv3.keepAlive).close` (`client/v3/lease.go`).

Users: `recvKeepAlive`, `recvKeepAliveLoop`'s cleanup, `deadlineLoop` (each under `l.mu`, the entry
just removed from the map).

Proof sketch: closes `donec` and every channel of the entry with the close tokens `kaEntry` holds.

Changes: from `specs-ref/Spec/go_etcd_io/etcd/client/v3/keepAlive__close.lean`: restated over
`kaEntry`.

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

/-- `ka.close()`: the entry's `donec` and channels closed (the entry consumed). -/
def keepAlive.close.spec : Prop :=
  ∀ (ka : Loc) (id : w64),
  {{ kaEntry (GF := GF) ka id }}
    (App (Val (ka @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.keepAlive.ty @!! go!"close"))
      (Val #()))
  {{ RET #(); True }}

end spec

end ClientV3
end EtcdGrove
end Perennial
