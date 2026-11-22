/-
`clientv3.RetryMaintenanceClient` (`client/v3/retry.go`, translated 2026-11-22 for `NewMaintenance`).
Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.client.v3.InvAuthConn

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

/-- `RetryMaintenanceClient(c, conn)` (`c` unused): a new `*retryMaintenanceClient` (over the
generated stub on `conn`), as a `MaintenanceClient`. -/
abbrev RetryMaintenanceClient.spec : Prop :=
  ∀ (cl conn : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 }}
    (App (App (Val (@! go_etcd_io.etcd.client.v3.RetryMaintenanceClient)) (Val #cl)) (Val #conn))
  {{ (v : GoInterface), RET #v; ∃ r : Loc,
      ⌜v = interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.client.v3.retryMaintenanceClient.ty) #r⌝ }}

end spec

end EtcdGrove
end Perennial
