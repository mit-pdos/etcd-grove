/-
`NewAuthClient(cc)` (`api/etcdserverpb/rpc_grpc.pb.go`, generated): the client stub of the Auth service.

Users: the client's `RetryAuthClient` (1c), `examples/etcd/auth`. Snippet: `examples/specreq/etcdserverpb/stubs.go`.

Proof sketch: the body allocates `&authClient{cc}`; persist it (`stubAt`). `remoteAuthAt` (the client's contract
of the service, `client/v3/Api*.lean`) of the result, per method: the stub's spec (`authClient.*.spec`,
WP form) reduces it to the connection's `Invoke`/`NewStream` of the method (grpc's
`ClientConn.Invoke.spec`/`NewStream.spec`, 2a, at `connOk`'s realization `connAt` with the client's
interceptors, 1c); the attempt goes to a member serving the method with etcd's contract
(`servesAt γ ep`, `V3rpc.etcdUnary γ m`, 2a), whose contents are related to the request's and the
reply's models by this batch's relations (`reqModels`, `replyModels`: the caller's `rangeReqOwn`
etc. through `*_msgAt`, the reply decoded into the stub's `new(T)` holding the member's content).

Changes: from `specs-ref/Spec/go_etcd_io/etcd/api/v3/etcdserverpb/NewAuthClient.lean`: the client-facing statement (the client's contract `remoteAuthAt`, not the stub's struct); the stub's struct is the method specs' (`stubAt`).
Margin: none.
-/
module

public import Spec.go_etcd_io.etcd.api.v3.etcdserverpb.Realize

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

/-- `NewAuthClient(conn)` over a client's connection: a stub meeting the client's contract. -/
def NewAuthClient.spec : Prop :=
  ∀ (conn : Loc) (γ : Cluster) (who : Principal),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.etcdserverpb ∗ ClientV3.connOk conn γ who }}
    (App (Val (@! etcdserverpb.NewAuthClient))
      (Val #(interface.mkOk (go.GoType.PointerType google_golang_org.grpc.ClientConn.ty) #conn)))
  {{ (v : GoInterface), RET #v; ClientV3.remoteAuthAt v γ who }}

end spec

end EtcdServerPb
end EtcdGrove
end Perennial
