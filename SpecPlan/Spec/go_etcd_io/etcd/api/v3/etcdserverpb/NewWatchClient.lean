/-
`NewWatchClient(cc)` (`api/etcdserverpb/rpc_grpc.pb.go`, generated): the client stub of the Watch service.

Users: the client's `NewWatcher` (`watch.go`: `pb.NewWatchClient(c.conn)`, 1b's `NewWatcher.spec`). Snippet: `examples/specreq/etcdserverpb/stubs.go`.

Proof sketch: the body allocates `&watchClient{cc}`; persist it (`stubAt`). `remoteWatchAt` (the client's contract
of the service, `client/v3/Api*.lean`) of the result, per method: the stub's spec (`watchClient.*.spec`,
WP form) reduces it to the connection's `Invoke`/`NewStream` of the method (grpc's
`ClientConn.Invoke.spec`/`NewStream.spec`, 2a, at `connOk`'s realization `connAt` with the client's
interceptors, 1c); the attempt goes to a member serving the method with etcd's contract
(`servesAt γ ep`, `V3rpc.etcdUnary γ m`, 2a), whose contents are related to the request's and the
reply's models by this batch's relations (`reqModels`, `replyModels`: the caller's `rangeReqOwn`
etc. through `*_msgAt`, the reply decoded into the stub's `new(T)` holding the member's content).

Changes: from `specs-ref/Spec/go_etcd_io/etcd/api/v3/etcdserverpb/NewWatchClient.lean`: the client-facing statement (the client's contract `remoteWatchAt`, not the stub's struct); the stub's struct is the method specs' (`stubAt`).
verify-round (client-watch's request W3): the contract is given once the client whose connection it is (`c.conn`) is ready (`□ (clientReady c -∗ …)`): the stub's calls go through the connection's interceptors, whose token refresh reads `c.Auth`, unset when `newClient` builds the stubs (`client.go:460-461`).
Margin: none.
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.api.v3.etcdserverpb.Realize

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace EtcdServerPb

open Iris Iris.BI EtcdModel EtcdWire
open go_etcd_io.etcd.api.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.api.v3.etcdserverpb.Assumptions]

/-- `NewWatchClient(conn)` over a client's connection: a stub meeting the client's contract. -/
def NewWatchClient.spec : Prop :=
  ∀ (conn c : Loc) (γ : Cluster) (who : Principal),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.etcdserverpb ∗ ClientV3.connOk conn γ who ∗
      ClientV3.clientConnOk c γ who ∗ c.[go_etcd_io.etcd.client.v3.Client, go!"conn"] ↦□ conn }}
    (App (Val (@! etcdserverpb.NewWatchClient))
      (Val #(interface.mkOk (go.GoType.PointerType google_golang_org.grpc.ClientConn.ty) #conn)))
  {{ (v : GoInterface), RET #v; □ (ClientV3.clientReady c -∗ ClientV3.remoteWatchAt v γ who) }}

end spec

end EtcdServerPb
end EtcdGrove
end Perennial
