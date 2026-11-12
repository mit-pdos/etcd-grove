/-
`(*EtcdServer).Config()` (`server.go:451-453`): a copy of `s.Cfg`.

**Users**: v3rpc's `maintenanceServer.Status` (its `DbSizeQuota`), embed.

**Proof sketch**: a read of the read-only `s.Cfg` (`isServer`'s realization: the whole struct,
including the two fields `start` defaults, is read-only once started).

**Changes**: verify round (A8-completeness F5): new.

Re-review (RR-server-core, found in the RR2 repair): over `isServer` (was `srvMember`): the copy reads
`SnapshotCount`/`SnapshotCatchUpEntries`, which `start` writes (`server.go:556,564`), so before
`start` a concurrent `Config()` would race; its users (maintenance `Status`, etcdhttp's health)
hold `isServer`.
**Margin**: the value is not tied to `NewServer`'s configuration (no user needs more than its type).
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.server.v3.etcdserver.ApiBoot

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace EtcdServer

open Iris Iris.BI EtcdModel

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **`Config()`**: a configuration value (any). -/
def EtcdServer.Config.spec : Prop :=
  ∀ (s : Loc) (γ : Cluster),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗ isServer s γ }}
    (App (Val (s @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.EtcdServer.ty @!!
      go!"Config")) (Val #()))
  {{ (c : go_etcd_io.etcd.server.v3.config.ServerConfig), RET #c; True }}

end spec

end EtcdServer
end EtcdGrove
end Perennial
