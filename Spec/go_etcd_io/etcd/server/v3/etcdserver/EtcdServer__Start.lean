/-
## `(*EtcdServer).Start()` (`server.go:530-543`)

**Users.** `embed.StartEtcd` (`embed/etcd.go:282`); `examples/lib/etcdstart` (`StartServer`,
`StartCompactingServer`, `StartPeriodicServer`, `StartMember`), `cluster3.StartMember`,
`restart.startMember`. Once per built server, before serving its gRPC API (`v3rpc.Server`, 2a,
takes `isServer`). Snippets: `etcdserverboot/boot.go`.

**Proof sketch.** `start()` (`EtcdServer.start.spec`: `isServer`, `srvRunning`, the publication's
and the purge's rights), then ten `GoAttach`es (`EtcdServer.GoAttach.spec`, each at `isServer`):
`adjustTicks`, `publishV3` (with `srvPublish`), `purgeFile` (`srvPurge`), `monitorFileDescriptor`
(the stopping channel: `StoppingNotify`'s), `monitorClusterVersions`, `monitorStorageVersion`, the
read loop (2c's `Read.LinearizableReadLoop`, with the loop's token from `isServer`'s realization),
`monitorKVHash`, `monitorCompactHash`, `monitorDowngrade`; each goroutine's WP from its spec (posts
`True`).

**Changes** (from `specs-ref`'s `EtcdServer__Start.lean`): over `srvBuilt` and the two lifecycle
predicates in place of the built part's eighteen conjuncts and the auth mode's parameter.

**Margin.** The post says nothing of liveness (the member publishing itself, the read loop
answering): `servesAt` (2a) and the request path's specs carry what clients see.
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

/-- **Starts the built server `s`**: it serves `γ` (`isServer`) until stopped, and the caller may
stop it (`srvRunning`). -/
def EtcdServer.Start.spec : Prop :=
  ∀ (s : Loc) (γ : Cluster) (id : Nat) (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗ srvBuilt s γ id cfg }}
    (App (Val (s @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.EtcdServer.ty @!! go!"Start")) (Val #()))
  {{ RET #(); isServer s γ ∗ srvRunning s γ id (Config.dirsOf cfg) }}

end spec

end EtcdServer
end EtcdGrove
end Perennial
