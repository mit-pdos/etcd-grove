/-
Trust boundary: `v3rpc.NewMaintenanceServer` (an axiom; see
`Spec/go_etcd_io/etcd/server/v3/etcdserver/api/v3rpc/NewMaintenanceServer.lean`). Translated with
its body (item 4, the server start), not proved: its `maintenanceServer` literal stores a
`serverversion.Server` (`etcdserver.NewServerVersionAdapter(s)`), a type the translation of
`etcdserver/version` axiomatizes (`version.toml` imports none of the packages its interface's
methods name), so the literal's field write does not reduce without the type's `sorry` instances.
Translating the interface (the imports `context`, `semver`, etcd's API `version`) changes
`version`'s initializer, which then initializes those packages: item 8's `wp_initialize'` chain
(`version`, `membership`, `api`, ...) would take `context`'s instance assumptions. Left to item 8.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.NewMaintenanceServer

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

/-- **Trust boundary** (item 4, the server start; see the file header): `NewMaintenanceServer(s,
hn)` reads `s.Cfg.Logger` (read-only), calls `s.KV()` (the field `kv`, read-only: the watchable
store) and its `HashStorage()` (`(*store).HashStorage`, promoted: the field `hashes`, set by
`NewStore` before the store is shared, never written), `newHeader(s)` (proved, over `raftKV`),
`etcdserver.NewServerVersionAdapter(s)` (an allocation), possibly `zap.NewNop()`, and allocates a
`maintenanceServer` and an `AuthAdmin`; it returns the new `*authMaintenanceServer` as a
`MaintenanceServer`. -/
axiom v3rpc.NewMaintenanceServer.wp_proof :
  v3rpc.NewMaintenanceServer.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
