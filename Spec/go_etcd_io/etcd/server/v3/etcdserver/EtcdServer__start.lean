/-
## `(*EtcdServer).start()` (`server.go:547-606`)

**Users.** `Start` only (and etcd's own unit tests).

**Proof sketch.** The snapshot settings defaulted (fields of `s.Cfg`, owned by `srvBuilt`); the
fields the request path reads made (`wait.New`, `wait.NewTimeList`, the `done`/`stop`/`stopping`
channels, `context.WithCancel`, `read.NewRead` over `s` and `s.r`, `notify.NewNotifier`: 2c's specs)
and frozen: with `srvBuilt`'s request-path slot they make `isServer s γ` (2c's realization: the
request path's invariant). `ClusterVersion` (logging only), then the compactor's `Run`
(`V3compactor`'s `isCompactor`: any number of times), and `go s.run()` with 2d's `run` precondition
(the raft node built, the apply thread's state, the scheduler: `srvBuilt`'s apply-thread slot; `run`'s
stop escrow deposits `memberDisk` in `s.done`'s closing, which `srvRunning` reads).

**Changes**: from `specs-ref`'s `EtcdServer__start.lean`: over `srvBuilt`.

**Margin.** As `Start`.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.ApiBoot

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

/-- **`start`**: the request path's fields built, the compactor and the apply loop started. -/
def EtcdServer.start.spec : Prop :=
  ∀ (s : Loc) (γ : Cluster) (id : Nat) (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗ srvBuilt s γ id cfg }}
    (App (Val (s @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.EtcdServer.ty @!! go!"start")) (Val #()))
  {{ RET #(); isServer s γ ∗ srvGate s 1 ∗ srvRunning s γ id (Config.dirsOf cfg) ∗ srvPublish s ∗
      srvPurge s }}

end spec

end EtcdServer
end EtcdGrove
end Perennial
