/-
## `(*EtcdServer).Stop()` (`server.go:1354-1360`): the graceful stop

**Users.** `embed.Etcd.Close` (`embed/etcd.go:470`); etcd's tests.

**Proof sketch.** `TryTransferLeadershipOnShutdown` (`isServer` from `srvRunning`'s realization: a
leader with other voters moves its leadership, `MoveLeader`: a raft step with no effect on the
model; its error is logged), then `HardStop.spec`.

**Changes**: new (no old spec).

**Margin.** As `HardStop`.
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

/-- **Stops `s` gracefully** (leadership moved first if it leads), as `HardStop`. -/
def EtcdServer.Stop.spec : Prop :=
  ∀ (s : Loc) (γ : Cluster) (id : Nat) (ds : Config.Dirs),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗ srvRunning s γ id ds ∗ srvGate s 1 }}
    (App (Val (s @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.EtcdServer.ty @!! go!"Stop")) (Val #()))
  {{ RET #(); memberDisk γ id ds }}

end spec

end EtcdServer
end EtcdGrove
end Perennial
