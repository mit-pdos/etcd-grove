/-
`etcdserverpb.NewMaintenanceClient(cc)` (`api/etcdserverpb/rpc_grpc.pb.go`, the generated Maintenance stub;
translated for `clientv3.RetryMaintenanceClient`, 2026-11-22). Lean-first (no Rocq counterpart).
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

/-- `NewMaintenanceClient(cc)`: a new `*maintenanceClient` whose `cc` is `cc` (read-only), as a `MaintenanceClient`. -/
abbrev NewMaintenanceClient.spec : Prop :=
  ∀ (cc : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.etcdserverpb }}
    (App (Val (@! etcdserverpb.NewMaintenanceClient)) (Val #cc))
  {{ (v : GoInterface), RET #v; ∃ ac : Loc,
      ⌜v = interface.mkOk (go.GoType.PointerType etcdserverpb.maintenanceClient.ty) #ac⌝ ∗
      structFieldRef etcdserverpb.maintenanceClient go!"cc" ac ↦□ cc }}

end spec

end EtcdGrove
end Perennial
