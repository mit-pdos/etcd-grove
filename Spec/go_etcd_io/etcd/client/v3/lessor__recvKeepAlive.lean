/-
`(*clientv3.lessor).recvKeepAlive` (`client/v3/lease.go`).

Users: `recvKeepAliveLoop`.

Proof sketch: a fresh `LeaseKeepAliveResponse` from the message's header, id and TTL, persisted
(shared by every channel of the entry: `kaRespAt` needs it read-only); under `l.mu`: no entry for
the id: nothing; TTL `≤ 0`: deletes and closes the entry (`keepAlive.close`); else a non-blocking
send on each of the entry's channels (each value meets `kaRespAt _ id`: the id the map was looked
up by, a positive TTL: the channel's invariant), the deadlines advanced.

Changes: from `specs-ref/Spec/go_etcd_io/etcd/client/v3/lessor__recvKeepAlive.lean`: restated over
`lessorHandle`; the values' facts (`kaRespAt`) new.

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

/-- `l.recvKeepAlive(resp)`: the response delivered to the lease's channels (or its entry closed
on a non-positive TTL). -/
def lessor.recvKeepAlive.spec : Prop :=
  ∀ (l : Loc) (γ : Cluster) (who : Principal) (p h : Loc) (id ttl : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ lessorHandle l γ who ∗
      protoRest go_etcd_io.etcd.api.v3.etcdserverpb.LeaseKeepAliveResponse p (DFrac.own 1) ∗
      p.[go_etcd_io.etcd.api.v3.etcdserverpb.LeaseKeepAliveResponse, go!"Header"] ↦ h ∗
      p.[go_etcd_io.etcd.api.v3.etcdserverpb.LeaseKeepAliveResponse, go!"ID"] ↦ id ∗
      p.[go_etcd_io.etcd.api.v3.etcdserverpb.LeaseKeepAliveResponse, go!"TTL"] ↦ ttl ∗
      hdrOwn h (DFrac.own 1) }}
    (App (Val (l @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.lessor.ty @!! go!"recvKeepAlive")) (Val #p))
  {{ RET #(); True }}

end spec

end ClientV3
end EtcdGrove
end Perennial
