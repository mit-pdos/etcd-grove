/-
`NewMaintenanceClient(cc)` (`api/etcdserverpb/rpc_grpc.pb.go`, generated): the client stub of the Maintenance service.

Users: the client's `RetryMaintenanceClient` and `maintenance`'s per-endpoint clients (`client/v3/maintenance.go`).

Proof sketch: the body allocates `&maintenanceClient{cc}`; persist it (`stubAt`). `remoteMaintAt` (the client's
contract of the service, `client/v3/ApiClient.lean`) of the result, per method: the stub's spec
(`maintenanceClient.*.spec`, WP form) reduces it to the connection's `Invoke`/`NewStream` of the method (grpc's
`ClientConn.Invoke.spec`/`NewStream.spec`, 2a, at `connOk`'s realization), as `NewAuthClient.spec`'s.
Blocked: the body is untranslated (names only in `Code/go_etcd_io/etcd/api/v3/etcdserverpb.toml`): the proof waits for its translation (open question 7.4).
Changes: verify-round: new (A6 completeness F1; 1c's request, `req/go_etcd_io_etcd_api_v3_etcdserverpb.md`
"from 1c" item 2), as `NewAuthClient.spec` (with client-watch's W3 shape: the contract once the client `c` whose
connection it is is ready, `□ (clientReady c -∗ …)`).
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

/-- `NewMaintenanceClient(conn)` over a client's connection: a stub meeting the client's contract. -/
def NewMaintenanceClient.spec : Prop :=
  ∀ (conn c : Loc) (γ : Cluster) (who : Principal),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.etcdserverpb ∗ ClientV3.connOk conn γ who ∗
      ClientV3.clientConnOk c γ who ∗ c.[go_etcd_io.etcd.client.v3.Client, go!"conn"] ↦□ conn }}
    (App (Val (@! etcdserverpb.NewMaintenanceClient))
      (Val #(interface.mkOk (go.GoType.PointerType google_golang_org.grpc.ClientConn.ty) #conn)))
  {{ (v : GoInterface), RET #v; □ (ClientV3.clientReady c -∗ ClientV3.remoteMaintAt v γ who) }}

end spec

end EtcdServerPb
end EtcdGrove
end Perennial
