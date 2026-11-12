/-
`v3rpc.NewMaintenanceServer` (`v3rpc/maintenance.go`; item 4, the server start). Lean-first (no Rocq counterpart); the
vocabulary is `Proof/go_etcd_io/etcd/server/v3/etcdserver/api/v3rpc/InvGrpcStart.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.InvGrpcStart

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver.api go_etcd_io.etcd.server.v3.etcdserver
  go_etcd_io.etcd.api.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

/-- **`NewMaintenanceServer(s, hn)`** returns a new `*authMaintenanceServer` as a
`MaintenanceServer` (over a `*maintenanceServer` holding the server in its roles, its KV's hash
storage, `newHeader(s)`, a version adapter and the health notifier `hn`). -/
abbrev v3rpc.NewMaintenanceServer.spec : Prop :=
  ∀ (s : Loc) (A : v3rpc.KVAns GF) (lg0 wsl : Loc) (hn : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗ v3rpc.raftKV s A ∗ srvCfgFieldAddr s go!"Logger" ↦□ lg0 ∗
      srvKVAddr s ↦□ v3rpc.wsIface wsl }}
    (App (App (Val (@! v3rpc.NewMaintenanceServer)) (Val #s)) (Val #hn))
  {{ (v : GoInterface), RET #v; ∃ p : Loc,
      ⌜v = interface.mkOk (go.GoType.PointerType v3rpc.authMaintenanceServer.ty) #p⌝ }}

end spec

end EtcdGrove
end Perennial
