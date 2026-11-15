/-
`v3rpc.maintenanceServer.Snapshot` (`server/etcdserver/api/v3rpc/`).

Users: grpc's run of `/etcdserverpb.Maintenance/Snapshot` (3h's handler); `etcdctl snapshot save`, the client's `Snapshot` (1c, not specified there).

Proof sketch: the storage version (4b's `schema`), the backend's snapshot (4a), an `io.Pipe` written by a goroutine (`go`, its token from `Fork`), chunks of `32 KiB` sent (`srvSend_send`, `dn` `True`), the SHA-256 last; errors through `togRPCError`.

Changes: new.

Margin: the bytes are not modelled (`snapSpec`).
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace V3rpc

open Iris Iris.BI EtcdModel EtcdWire ClientV3 Grpc Proto EtcdServer

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- `p.Snapshot(sr, srv)`: a run of the snapshot stream. -/
def maintenanceServer.Snapshot.spec : Prop :=
  ∀ (p s : Loc) (γ : Cluster) (sr : Loc) (c : Content) (st : GoInterface) (g : StreamName) (md : MD),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗ maintAt p s γ ∗ threadTok ∗ msgAt go_etcd_io.etcd.api.v3.etcdserverpb.SnapshotRequest.ty sr (DFrac.own 1) c ∗
      (∃ ctx, srvCtxOf st ctx md) ∗ srvRecv st g snapSpec md 1 ∗ srvSend st g snapSpec md 0 }}
    (App (App (Val (p @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.maintenanceServer.ty @!! go!"Snapshot")) (Val #sr)) (Val #st))
  {{ (err : GoInterface), RET #err; threadTok ∗ streamOut st g snapSpec md err }}

end spec

end V3rpc
end EtcdGrove
end Perennial
