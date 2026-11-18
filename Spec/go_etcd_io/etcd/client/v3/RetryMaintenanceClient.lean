/-
`clientv3.RetryMaintenanceClient(c, conn)` (`client/v3/retry.go`: `&retryMaintenanceClient{mc:
pb.NewMaintenanceClient(conn)}`). Lean-first (axiom-triage, 2026-11-18: `NewMaintenance` calls it).
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

/-- `RetryMaintenanceClient(c, conn)` returns. -/
abbrev RetryMaintenanceClient.spec : Prop :=
  ∀ (cl conn : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 }}
    (App (App (Val (@! go_etcd_io.etcd.client.v3.RetryMaintenanceClient)) (Val #cl)) (Val #conn))
  {{ (v : GoInterface), RET #v; True }}

end spec

end EtcdGrove
end Perennial
