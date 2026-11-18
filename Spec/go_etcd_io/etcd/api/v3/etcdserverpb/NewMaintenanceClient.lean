/-
`etcdserverpb.NewMaintenanceClient(cc)` (`api/etcdserverpb/rpc_grpc.pb.go`: `&maintenanceClient{cc}`, the
generated Maintenance stub). Lean-first (axiom-triage, 2026-11-18: the client's `NewMaintenance` calls it).
-/
module

public import Proof.go_etcd_io.etcd.client.v3.InvClientNew

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.api.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- `NewMaintenanceClient(cc)` returns (a new `*maintenanceClient`, as a `MaintenanceClient`). -/
abbrev NewMaintenanceClient.spec : Prop :=
  ∀ (cc : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.etcdserverpb }}
    (App (Val (@! etcdserverpb.NewMaintenanceClient)) (Val #cc))
  {{ (v : GoInterface), RET #v; True }}

end spec

end EtcdGrove
end Perennial
